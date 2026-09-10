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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(lean_object* v_fvarId_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
lean_dec_ref_known(v___x_11_, 1);
v___x_13_ = l_Lean_Meta_Tactic_Cbv_cbvHyp(v_a_12_, v_fvarId_1_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v_a_16_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
if (lean_obj_tag(v_a_14_) == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
v_a_16_ = v___x_27_;
goto v___jp_15_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_val_28_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v_a_14_, 1);
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v_val_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v_a_16_ = v___x_30_;
goto v___jp_15_;
}
v___jp_15_:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_16_, v___y_3_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_25_; 
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
lean_object* v_unused_26_; 
v_unused_26_ = lean_ctor_get(v___x_17_, 0);
lean_dec(v_unused_26_);
v___x_19_ = v___x_17_;
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
else
{
lean_dec(v___x_17_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_box(0);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_21_);
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
else
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_13_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_13_);
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
v_a_39_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_11_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_11_);
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
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_82_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_a_91_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v_a_95_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_92_, 1);
if (lean_obj_tag(v_a_93_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
v_a_95_ = v___x_106_;
goto v___jp_94_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_val_107_ = lean_ctor_get(v_a_93_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_a_93_, 1);
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v_val_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v_a_95_ = v___x_109_;
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_95_, v___y_82_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_96_, 0);
lean_dec(v_unused_105_);
v___x_98_ = v___x_96_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_dec(v___x_96_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_box(0);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
return v___x_96_;
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_92_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_92_);
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
v_a_118_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_90_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_90_);
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
lean_object* v___x_178_; lean_object* v_env_179_; lean_object* v___x_180_; lean_object* v_toCold_181_; lean_object* v_mctx_182_; lean_object* v_lctx_183_; lean_object* v_options_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_env_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_179_);
lean_dec(v___x_178_);
v___x_180_ = lean_st_ref_get(v___y_174_);
v_toCold_181_ = lean_ctor_get(v___y_175_, 0);
v_mctx_182_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_mctx_182_);
lean_dec(v___x_180_);
v_lctx_183_ = lean_ctor_get(v___y_173_, 2);
v_options_184_ = lean_ctor_get(v_toCold_181_, 2);
lean_inc_ref(v_options_184_);
lean_inc_ref(v_lctx_183_);
v___x_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_185_, 0, v_env_179_);
lean_ctor_set(v___x_185_, 1, v_mctx_182_);
lean_ctor_set(v___x_185_, 2, v_lctx_183_);
lean_ctor_set(v___x_185_, 3, v_options_184_);
v___x_186_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_msgData_172_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0___boxed(lean_object* v_msgData_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msgData_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_ref_201_; lean_object* v___x_202_; lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_ref_201_ = lean_ctor_get(v___y_198_, 2);
v___x_202_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_inc(v_ref_201_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v_ref_201_);
lean_ctor_set(v___x_207_, 1, v_a_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 1);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg___boxed(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_218_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0));
v___x_221_ = l_Lean_stringToMessageData(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(lean_object* v_x_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1);
v___x_233_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v___x_232_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(v_x_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v_x_234_);
return v_res_244_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(lean_object* v_a_245_, lean_object* v_as_246_, size_t v_i_247_, size_t v_stop_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = lean_usize_dec_eq(v_i_247_, v_stop_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_array_uget_borrowed(v_as_246_, v_i_247_);
v___x_251_ = l_Lean_instBEqFVarId_beq(v_a_245_, v___x_250_);
if (v___x_251_ == 0)
{
size_t v___x_252_; size_t v___x_253_; 
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_add(v_i_247_, v___x_252_);
v_i_247_ = v___x_253_;
goto _start;
}
else
{
return v___x_251_;
}
}
else
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2___boxed(lean_object* v_a_256_, lean_object* v_as_257_, lean_object* v_i_258_, lean_object* v_stop_259_){
_start:
{
size_t v_i_boxed_260_; size_t v_stop_boxed_261_; uint8_t v_res_262_; lean_object* v_r_263_; 
v_i_boxed_260_ = lean_unbox_usize(v_i_258_);
lean_dec(v_i_258_);
v_stop_boxed_261_ = lean_unbox_usize(v_stop_259_);
lean_dec(v_stop_259_);
v_res_262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_256_, v_as_257_, v_i_boxed_260_, v_stop_boxed_261_);
lean_dec_ref(v_as_257_);
lean_dec(v_a_256_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object* v_as_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_array_get_size(v_as_264_);
v___x_268_ = lean_nat_dec_lt(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
return v___x_268_;
}
else
{
if (v___x_268_ == 0)
{
return v___x_268_;
}
else
{
size_t v___x_269_; size_t v___x_270_; uint8_t v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_267_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_265_, v_as_264_, v___x_269_, v___x_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object* v_as_272_, lean_object* v_a_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_as_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_as_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object* v_wildcardHyps_x3f_276_, lean_object* v_fvarId_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
if (lean_obj_tag(v_wildcardHyps_x3f_276_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_val_287_ = lean_ctor_get(v_wildcardHyps_x3f_276_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_wildcardHyps_x3f_276_);
if (v_isSharedCheck_297_ == 0)
{
v___x_289_ = v_wildcardHyps_x3f_276_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v_wildcardHyps_x3f_276_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
uint8_t v___x_291_; 
v___x_291_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_val_287_, v_fvarId_277_);
lean_dec(v_val_287_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_fvarId_277_);
v___x_292_ = lean_box(0);
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 0);
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v___x_296_; 
lean_del_object(v___x_289_);
v___x_296_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_296_;
}
}
}
else
{
lean_object* v___x_298_; 
lean_dec(v_wildcardHyps_x3f_276_);
v___x_298_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object* v_wildcardHyps_x3f_299_, lean_object* v_fvarId_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(v_wildcardHyps_x3f_299_, v_fvarId_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_319_, uint8_t v___y_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 1)
{
lean_object* v_pre_322_; 
v_pre_322_ = lean_ctor_get(v_x_321_, 0);
switch(lean_obj_tag(v_pre_322_))
{
case 1:
{
lean_object* v_pre_323_; 
v_pre_323_ = lean_ctor_get(v_pre_322_, 0);
switch(lean_obj_tag(v_pre_323_))
{
case 0:
{
lean_object* v_str_324_; lean_object* v_str_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_str_324_ = lean_ctor_get(v_x_321_, 1);
v_str_325_ = lean_ctor_get(v_pre_322_, 1);
v___x_326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_327_ = lean_string_dec_eq(v_str_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_329_ = lean_string_dec_eq(v_str_325_, v___x_328_);
if (v___x_329_ == 0)
{
return v___x_329_;
}
else
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_331_ = lean_string_dec_eq(v_str_324_, v___x_330_);
if (v___x_331_ == 0)
{
return v___x_331_;
}
else
{
return v_suppressElabErrors_319_;
}
}
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_333_ = lean_string_dec_eq(v_str_324_, v___x_332_);
if (v___x_333_ == 0)
{
return v___x_333_;
}
else
{
return v_suppressElabErrors_319_;
}
}
}
case 1:
{
lean_object* v_pre_334_; 
v_pre_334_ = lean_ctor_get(v_pre_323_, 0);
if (lean_obj_tag(v_pre_334_) == 0)
{
lean_object* v_str_335_; lean_object* v_str_336_; lean_object* v_str_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_str_335_ = lean_ctor_get(v_x_321_, 1);
v_str_336_ = lean_ctor_get(v_pre_322_, 1);
v_str_337_ = lean_ctor_get(v_pre_323_, 1);
v___x_338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_339_ = lean_string_dec_eq(v_str_337_, v___x_338_);
if (v___x_339_ == 0)
{
return v___x_339_;
}
else
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_341_ = lean_string_dec_eq(v_str_336_, v___x_340_);
if (v___x_341_ == 0)
{
return v___x_341_;
}
else
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6));
v___x_343_ = lean_string_dec_eq(v_str_335_, v___x_342_);
if (v___x_343_ == 0)
{
return v___x_343_;
}
else
{
return v_suppressElabErrors_319_;
}
}
}
}
else
{
return v___y_320_;
}
}
default: 
{
return v___y_320_;
}
}
}
case 0:
{
lean_object* v_str_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_str_344_ = lean_ctor_get(v_x_321_, 1);
v___x_345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7));
v___x_346_ = lean_string_dec_eq(v_str_344_, v___x_345_);
if (v___x_346_ == 0)
{
return v___x_346_;
}
else
{
return v_suppressElabErrors_319_;
}
}
default: 
{
return v___y_320_;
}
}
}
else
{
return v___y_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_347_, lean_object* v___y_348_, lean_object* v_x_349_){
_start:
{
uint8_t v_suppressElabErrors_boxed_350_; uint8_t v___y_7543__boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_suppressElabErrors_boxed_350_ = lean_unbox(v_suppressElabErrors_347_);
v___y_7543__boxed_351_ = lean_unbox(v___y_348_);
v_res_352_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_350_, v___y_7543__boxed_351_, v_x_349_);
lean_dec(v_x_349_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(lean_object* v_ref_355_, lean_object* v_msgData_356_, uint8_t v_severity_357_, uint8_t v_isSilent_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_402_; lean_object* v___y_403_; uint8_t v___y_404_; uint8_t v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_427_; lean_object* v___y_428_; uint8_t v___y_429_; uint8_t v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; uint8_t v___y_433_; lean_object* v___y_434_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v___y_442_; uint8_t v___y_443_; uint8_t v___y_444_; uint8_t v___x_449_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; uint8_t v___y_455_; uint8_t v___y_456_; uint8_t v___y_457_; uint8_t v___y_459_; uint8_t v___x_475_; 
v___x_449_ = 2;
v___x_475_ = l_Lean_instBEqMessageSeverity_beq(v_severity_357_, v___x_449_);
if (v___x_475_ == 0)
{
v___y_459_ = v___x_475_;
goto v___jp_458_;
}
else
{
uint8_t v___x_476_; 
lean_inc_ref(v_msgData_356_);
v___x_476_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_356_);
v___y_459_ = v___x_476_;
goto v___jp_458_;
}
v___jp_364_:
{
lean_object* v___x_374_; lean_object* v_toCold_375_; lean_object* v_currNamespace_376_; lean_object* v_openDecls_377_; lean_object* v_env_378_; lean_object* v_nextMacroScope_379_; lean_object* v_ngen_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_traceState_382_; lean_object* v_cache_383_; lean_object* v_messages_384_; lean_object* v_infoState_385_; lean_object* v_snapshotTasks_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_400_; 
v___x_374_ = lean_st_ref_take(v___y_373_);
v_toCold_375_ = lean_ctor_get(v___y_372_, 0);
v_currNamespace_376_ = lean_ctor_get(v_toCold_375_, 4);
v_openDecls_377_ = lean_ctor_get(v_toCold_375_, 5);
v_env_378_ = lean_ctor_get(v___x_374_, 0);
v_nextMacroScope_379_ = lean_ctor_get(v___x_374_, 1);
v_ngen_380_ = lean_ctor_get(v___x_374_, 2);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_374_, 3);
v_traceState_382_ = lean_ctor_get(v___x_374_, 4);
v_cache_383_ = lean_ctor_get(v___x_374_, 5);
v_messages_384_ = lean_ctor_get(v___x_374_, 6);
v_infoState_385_ = lean_ctor_get(v___x_374_, 7);
v_snapshotTasks_386_ = lean_ctor_get(v___x_374_, 8);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_400_ == 0)
{
v___x_388_ = v___x_374_;
v_isShared_389_ = v_isSharedCheck_400_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snapshotTasks_386_);
lean_inc(v_infoState_385_);
lean_inc(v_messages_384_);
lean_inc(v_cache_383_);
lean_inc(v_traceState_382_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_ngen_380_);
lean_inc(v_nextMacroScope_379_);
lean_inc(v_env_378_);
lean_dec(v___x_374_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_400_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
lean_inc(v_openDecls_377_);
lean_inc(v_currNamespace_376_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_currNamespace_376_);
lean_ctor_set(v___x_390_, 1, v_openDecls_377_);
v___x_391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___y_365_);
lean_inc_ref(v___y_366_);
lean_inc_ref(v___y_371_);
v___x_392_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_392_, 0, v___y_371_);
lean_ctor_set(v___x_392_, 1, v___y_370_);
lean_ctor_set(v___x_392_, 2, v___y_369_);
lean_ctor_set(v___x_392_, 3, v___y_366_);
lean_ctor_set(v___x_392_, 4, v___x_391_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5, v___y_368_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5 + 1, v___y_367_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5 + 2, v_isSilent_358_);
v___x_393_ = l_Lean_MessageLog_add(v___x_392_, v_messages_384_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 6, v___x_393_);
v___x_395_ = v___x_388_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_env_378_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextMacroScope_379_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_ngen_380_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_traceState_382_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_infoState_385_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_snapshotTasks_386_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_st_ref_put(v___y_373_, v___x_395_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
v___jp_401_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_425_; 
v___x_410_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_356_);
v___x_411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v___x_410_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_425_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_425_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_425_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_inc_ref_n(v___y_403_, 2);
v___x_416_ = l_Lean_FileMap_toPosition(v___y_403_, v___y_406_);
lean_dec(v___y_406_);
v___x_417_ = l_Lean_FileMap_toPosition(v___y_403_, v___y_409_);
lean_dec(v___y_409_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0));
if (v___y_408_ == 0)
{
lean_del_object(v___x_414_);
lean_dec_ref(v___y_402_);
v___y_365_ = v_a_412_;
v___y_366_ = v___x_419_;
v___y_367_ = v___y_405_;
v___y_368_ = v___y_404_;
v___y_369_ = v___x_418_;
v___y_370_ = v___x_416_;
v___y_371_ = v___y_407_;
v___y_372_ = v___y_361_;
v___y_373_ = v___y_362_;
goto v___jp_364_;
}
else
{
uint8_t v___x_420_; 
lean_inc(v_a_412_);
v___x_420_ = l_Lean_MessageData_hasTag(v___y_402_, v_a_412_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_423_; 
lean_dec_ref_known(v___x_418_, 1);
lean_dec_ref(v___x_416_);
lean_dec(v_a_412_);
v___x_421_ = lean_box(0);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_421_);
v___x_423_ = v___x_414_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_del_object(v___x_414_);
v___y_365_ = v_a_412_;
v___y_366_ = v___x_419_;
v___y_367_ = v___y_405_;
v___y_368_ = v___y_404_;
v___y_369_ = v___x_418_;
v___y_370_ = v___x_416_;
v___y_371_ = v___y_407_;
v___y_372_ = v___y_361_;
v___y_373_ = v___y_362_;
goto v___jp_364_;
}
}
}
}
v___jp_426_:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Syntax_getTailPos_x3f(v___y_431_, v___y_430_);
lean_dec(v___y_431_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_inc(v___y_434_);
v___y_402_ = v___y_427_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_433_;
v___y_409_ = v___y_434_;
goto v___jp_401_;
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
v___y_402_ = v___y_427_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_433_;
v___y_409_ = v_val_436_;
goto v___jp_401_;
}
}
v___jp_437_:
{
lean_object* v_ref_445_; lean_object* v___x_446_; 
v_ref_445_ = l_Lean_replaceRef(v_ref_355_, v___y_440_);
v___x_446_ = l_Lean_Syntax_getPos_x3f(v_ref_445_, v___y_441_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___y_427_ = v___y_438_;
v___y_428_ = v___y_439_;
v___y_429_ = v___y_444_;
v___y_430_ = v___y_441_;
v___y_431_ = v_ref_445_;
v___y_432_ = v___y_442_;
v___y_433_ = v___y_443_;
v___y_434_ = v___x_447_;
goto v___jp_426_;
}
else
{
lean_object* v_val_448_; 
v_val_448_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v___x_446_, 1);
v___y_427_ = v___y_438_;
v___y_428_ = v___y_439_;
v___y_429_ = v___y_444_;
v___y_430_ = v___y_441_;
v___y_431_ = v_ref_445_;
v___y_432_ = v___y_442_;
v___y_433_ = v___y_443_;
v___y_434_ = v_val_448_;
goto v___jp_426_;
}
}
v___jp_450_:
{
if (v___y_457_ == 0)
{
v___y_438_ = v___y_452_;
v___y_439_ = v___y_451_;
v___y_440_ = v___y_454_;
v___y_441_ = v___y_455_;
v___y_442_ = v___y_453_;
v___y_443_ = v___y_456_;
v___y_444_ = v_severity_357_;
goto v___jp_437_;
}
else
{
v___y_438_ = v___y_452_;
v___y_439_ = v___y_451_;
v___y_440_ = v___y_454_;
v___y_441_ = v___y_455_;
v___y_442_ = v___y_453_;
v___y_443_ = v___y_456_;
v___y_444_ = v___x_449_;
goto v___jp_437_;
}
}
v___jp_458_:
{
if (v___y_459_ == 0)
{
lean_object* v_toCold_460_; lean_object* v_ref_461_; uint8_t v_suppressElabErrors_462_; lean_object* v_fileName_463_; lean_object* v_fileMap_464_; lean_object* v_options_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___f_468_; uint8_t v___x_469_; uint8_t v___x_470_; 
v_toCold_460_ = lean_ctor_get(v___y_361_, 0);
v_ref_461_ = lean_ctor_get(v___y_361_, 2);
v_suppressElabErrors_462_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*3 + 1);
v_fileName_463_ = lean_ctor_get(v_toCold_460_, 0);
v_fileMap_464_ = lean_ctor_get(v_toCold_460_, 1);
v_options_465_ = lean_ctor_get(v_toCold_460_, 2);
v___x_466_ = lean_box(v_suppressElabErrors_462_);
v___x_467_ = lean_box(v___y_459_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_468_, 0, v___x_466_);
lean_closure_set(v___f_468_, 1, v___x_467_);
v___x_469_ = 1;
v___x_470_ = l_Lean_instBEqMessageSeverity_beq(v_severity_357_, v___x_469_);
if (v___x_470_ == 0)
{
v___y_451_ = v_fileMap_464_;
v___y_452_ = v___f_468_;
v___y_453_ = v_fileName_463_;
v___y_454_ = v_ref_461_;
v___y_455_ = v___y_459_;
v___y_456_ = v_suppressElabErrors_462_;
v___y_457_ = v___x_470_;
goto v___jp_450_;
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = l_Lean_warningAsError;
v___x_472_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_options_465_, v___x_471_);
v___y_451_ = v_fileMap_464_;
v___y_452_ = v___f_468_;
v___y_453_ = v_fileName_463_;
v___y_454_ = v_ref_461_;
v___y_455_ = v___y_459_;
v___y_456_ = v_suppressElabErrors_462_;
v___y_457_ = v___x_472_;
goto v___jp_450_;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref(v_msgData_356_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___boxed(lean_object* v_ref_477_, lean_object* v_msgData_478_, lean_object* v_severity_479_, lean_object* v_isSilent_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
uint8_t v_severity_boxed_486_; uint8_t v_isSilent_boxed_487_; lean_object* v_res_488_; 
v_severity_boxed_486_ = lean_unbox(v_severity_479_);
v_isSilent_boxed_487_ = lean_unbox(v_isSilent_480_);
v_res_488_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_477_, v_msgData_478_, v_severity_boxed_486_, v_isSilent_boxed_487_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v_ref_477_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(lean_object* v_ref_489_, lean_object* v_msgData_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; 
v___x_500_ = 1;
v___x_501_ = 0;
v___x_502_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_489_, v_msgData_490_, v___x_500_, v___x_501_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3___boxed(lean_object* v_ref_503_, lean_object* v_msgData_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_ref_503_, v_msgData_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v_ref_503_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1));
v___x_519_ = l_Lean_MessageData_ofFormat(v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(lean_object* v___f_520_, lean_object* v_stx_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___y_532_; lean_object* v_wildcardHyps_x3f_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v_toCold_579_; lean_object* v_options_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_toCold_579_ = lean_ctor_get(v___y_528_, 0);
v_options_580_ = lean_ctor_get(v_toCold_579_, 2);
v___x_581_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_582_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_options_580_, v___x_581_);
if (v___x_582_ == 0)
{
v___y_546_ = v___y_522_;
v___y_547_ = v___y_523_;
v___y_548_ = v___y_524_;
v___y_549_ = v___y_525_;
v___y_550_ = v___y_526_;
v___y_551_ = v___y_527_;
v___y_552_ = v___y_528_;
v___y_553_ = v___y_529_;
goto v___jp_545_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2);
v___x_584_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_521_, v___x_583_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_dec_ref_known(v___x_584_, 1);
v___y_546_ = v___y_522_;
v___y_547_ = v___y_523_;
v___y_548_ = v___y_524_;
v___y_549_ = v___y_525_;
v___y_550_ = v___y_526_;
v___y_551_ = v___y_527_;
v___y_552_ = v___y_528_;
v___y_553_ = v___y_529_;
goto v___jp_545_;
}
else
{
lean_dec_ref(v___f_520_);
return v___x_584_;
}
}
v___jp_531_:
{
lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___f_542_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed), 11, 1);
lean_closure_set(v___f_542_, 0, v_wildcardHyps_x3f_533_);
v___x_543_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed), 9, 0);
v___x_544_ = l_Lean_Elab_Tactic_withLocation(v___y_532_, v___f_542_, v___x_543_, v___f_520_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_532_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l_Lean_Syntax_getArg(v_stx_521_, v___x_554_);
v___x_556_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_555_);
lean_dec(v___x_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_547_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = l_Lean_MVarId_getNondepPropHyps(v_a_558_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_a_560_);
v___y_532_ = v___x_556_;
v_wildcardHyps_x3f_533_ = v___x_561_;
v___y_534_ = v___y_546_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_548_;
v___y_537_ = v___y_549_;
v___y_538_ = v___y_550_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___y_553_;
goto v___jp_531_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v___f_520_);
v_a_562_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_559_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v___f_520_);
v_a_570_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_557_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_557_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
v___y_532_ = v___x_556_;
v_wildcardHyps_x3f_533_ = v___x_578_;
v___y_534_ = v___y_546_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_548_;
v___y_537_ = v___y_549_;
v___y_538_ = v___y_550_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___y_553_;
goto v___jp_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed(lean_object* v___f_585_, lean_object* v_stx_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(v___f_585_, v_stx_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v_stx_586_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object* v_stx_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v___f_608_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0));
v___f_609_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_609_, 0, v___f_608_);
lean_closure_set(v___f_609_, 1, v_stx_598_);
v___x_610_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_609_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
return v___x_610_;
}
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object* v_00_u03b1_622_, lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_623_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object* v_00_u03b1_634_, lean_object* v_msg_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_00_u03b1_634_, v_msg_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(lean_object* v_ref_646_, lean_object* v_msgData_647_, uint8_t v_severity_648_, uint8_t v_isSilent_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_646_, v_msgData_647_, v_severity_648_, v_isSilent_649_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___boxed(lean_object* v_ref_660_, lean_object* v_msgData_661_, lean_object* v_severity_662_, lean_object* v_isSilent_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v_severity_boxed_673_; uint8_t v_isSilent_boxed_674_; lean_object* v_res_675_; 
v_severity_boxed_673_ = lean_unbox(v_severity_662_);
v_isSilent_boxed_674_ = lean_unbox(v_isSilent_663_);
v_res_675_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(v_ref_660_, v_msgData_661_, v_severity_boxed_673_, v_isSilent_boxed_674_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_ref_660_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1(){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_693_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3));
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6));
v___x_696_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___boxed), 10, 0);
v___x_697_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_693_, v___x_694_, v___x_695_, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
return v_res_699_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
v___x_701_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object* v_00_u03b1_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object* v_00_u03b1_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(v_00_u03b1_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_ref_736_; lean_object* v___x_737_; lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
v_ref_736_ = lean_ctor_get(v___y_733_, 2);
v___x_737_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_746_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_inc(v_ref_736_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_ref_736_);
lean_ctor_set(v___x_742_, 1, v_a_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 1);
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(lean_object* v_x_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1);
v___x_764_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v___x_763_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(lean_object* v_x_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(v_x_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v_x_765_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(uint8_t v___x_775_, lean_object* v___f_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___y_787_; lean_object* v___x_799_; 
v___x_799_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_778_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; uint8_t v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v___x_801_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1));
v___x_802_ = 0;
v___x_803_ = 0;
v___x_804_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_804_, 0, v___x_802_);
lean_ctor_set_uint8(v___x_804_, 1, v___x_775_);
lean_ctor_set_uint8(v___x_804_, 2, v___x_803_);
lean_ctor_set_uint8(v___x_804_, 3, v___x_775_);
v___x_805_ = l_Lean_MVarId_applyConst(v_a_800_, v___x_801_, v___x_804_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
if (lean_obj_tag(v_a_806_) == 1)
{
lean_object* v_tail_807_; 
v_tail_807_ = lean_ctor_get(v_a_806_, 1);
if (lean_obj_tag(v_tail_807_) == 0)
{
lean_object* v_head_808_; lean_object* v___x_809_; 
lean_dec_ref(v___f_776_);
v_head_808_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_head_808_);
lean_dec_ref_known(v_a_806_, 2);
v___x_809_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_head_808_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
v___y_787_ = v___x_809_;
goto v___jp_786_;
}
else
{
lean_object* v___x_810_; 
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
v___x_810_ = lean_apply_6(v___f_776_, v_a_806_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
v___y_787_ = v___x_810_;
goto v___jp_786_;
}
}
else
{
lean_object* v___x_811_; 
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
v___x_811_ = lean_apply_6(v___f_776_, v_a_806_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
v___y_787_ = v___x_811_;
goto v___jp_786_;
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v___f_776_);
v_a_812_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_805_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_805_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v___f_776_);
v_a_820_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_799_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_799_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
v___jp_786_:
{
if (lean_obj_tag(v___y_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___y_787_, 1);
v___x_788_ = lean_box(0);
v___x_789_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_788_, v___y_778_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_798_);
v___x_791_ = v___x_789_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_box(0);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
return v___x_789_;
}
}
else
{
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v___y_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(lean_object* v___x_828_, lean_object* v___f_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_1695__boxed_839_; lean_object* v_res_840_; 
v___x_1695__boxed_839_ = lean_unbox(v___x_828_);
v_res_840_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(v___x_1695__boxed_839_, v___f_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_840_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1));
v___x_845_ = l_Lean_MessageData_ofFormat(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(lean_object* v___f_846_, lean_object* v_stx_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_toCold_857_; lean_object* v_options_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_toCold_857_ = lean_ctor_get(v___y_854_, 0);
v_options_858_ = lean_ctor_get(v_toCold_857_, 2);
v___x_859_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_860_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_options_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_846_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2);
v___x_863_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_847_, v___x_862_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_864_; 
lean_dec_ref_known(v___x_863_, 1);
v___x_864_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_846_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
return v___x_864_;
}
else
{
lean_dec_ref(v___f_846_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(lean_object* v___f_865_, lean_object* v_stx_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(v___f_865_, v_stx_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_stx_866_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object* v_stx_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
lean_inc(v_stx_884_);
v___x_895_ = l_Lean_Syntax_isOfKind(v_stx_884_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_stx_884_);
v___x_896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_896_;
}
else
{
lean_object* v___f_897_; lean_object* v___x_898_; lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___x_901_; 
v___f_897_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2));
v___x_898_ = lean_box(v___x_895_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed), 11, 2);
lean_closure_set(v___f_899_, 0, v___x_898_);
lean_closure_set(v___f_899_, 1, v___f_897_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_900_, 0, v___f_899_);
lean_closure_set(v___f_900_, 1, v_stx_884_);
v___x_901_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_900_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object* v_stx_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(v_stx_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object* v_00_u03b1_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object* v_00_u03b1_921_, lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(v_00_u03b1_921_, v_msg_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1(){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1));
v___x_940_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed), 10, 0);
v___x_941_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_937_, v___x_938_, v___x_939_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
return v_res_943_;
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
