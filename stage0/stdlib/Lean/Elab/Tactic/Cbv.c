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
lean_object* v___x_178_; lean_object* v_env_179_; lean_object* v___x_180_; lean_object* v_mctx_181_; lean_object* v_lctx_182_; lean_object* v_options_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_env_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_179_);
lean_dec(v___x_178_);
v___x_180_ = lean_st_ref_get(v___y_174_);
v_mctx_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_mctx_181_);
lean_dec(v___x_180_);
v_lctx_182_ = lean_ctor_get(v___y_173_, 2);
v_options_183_ = lean_ctor_get(v___y_175_, 1);
lean_inc_ref(v_options_183_);
lean_inc_ref(v_lctx_182_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v_env_179_);
lean_ctor_set(v___x_184_, 1, v_mctx_181_);
lean_ctor_set(v___x_184_, 2, v_lctx_182_);
lean_ctor_set(v___x_184_, 3, v_options_183_);
v___x_185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_msgData_172_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0___boxed(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msgData_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_ref_200_ = lean_ctor_get(v___y_197_, 4);
v___x_201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_inc(v_ref_200_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_ref_200_);
lean_ctor_set(v___x_206_, 1, v_a_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 1);
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg___boxed(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(lean_object* v_x_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1);
v___x_232_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v___x_231_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object* v_x_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(v_x_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v_x_233_);
return v_res_243_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(lean_object* v_a_244_, lean_object* v_as_245_, size_t v_i_246_, size_t v_stop_247_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_usize_dec_eq(v_i_246_, v_stop_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_uget_borrowed(v_as_245_, v_i_246_);
v___x_250_ = l_Lean_instBEqFVarId_beq(v_a_244_, v___x_249_);
if (v___x_250_ == 0)
{
size_t v___x_251_; size_t v___x_252_; 
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_246_, v___x_251_);
v_i_246_ = v___x_252_;
goto _start;
}
else
{
return v___x_250_;
}
}
else
{
uint8_t v___x_254_; 
v___x_254_ = 0;
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2___boxed(lean_object* v_a_255_, lean_object* v_as_256_, lean_object* v_i_257_, lean_object* v_stop_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_stop_boxed_260_; uint8_t v_res_261_; lean_object* v_r_262_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_258_);
lean_dec(v_stop_258_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_255_, v_as_256_, v_i_boxed_259_, v_stop_boxed_260_);
lean_dec_ref(v_as_256_);
lean_dec(v_a_255_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object* v_as_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_array_get_size(v_as_263_);
v___x_267_ = lean_nat_dec_lt(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
return v___x_267_;
}
else
{
if (v___x_267_ == 0)
{
return v___x_267_;
}
else
{
size_t v___x_268_; size_t v___x_269_; uint8_t v___x_270_; 
v___x_268_ = ((size_t)0ULL);
v___x_269_ = lean_usize_of_nat(v___x_266_);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_264_, v_as_263_, v___x_268_, v___x_269_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object* v_as_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_as_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_as_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object* v_wildcardHyps_x3f_275_, lean_object* v_fvarId_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
if (lean_obj_tag(v_wildcardHyps_x3f_275_) == 1)
{
lean_object* v_val_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_val_286_ = lean_ctor_get(v_wildcardHyps_x3f_275_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_wildcardHyps_x3f_275_);
if (v_isSharedCheck_296_ == 0)
{
v___x_288_ = v_wildcardHyps_x3f_275_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_val_286_);
lean_dec(v_wildcardHyps_x3f_275_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; 
v___x_290_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_val_286_, v_fvarId_276_);
lean_dec(v_val_286_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec(v_fvarId_276_);
v___x_291_ = lean_box(0);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 0);
lean_ctor_set(v___x_288_, 0, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
lean_object* v___x_295_; 
lean_del_object(v___x_288_);
v___x_295_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_295_;
}
}
}
else
{
lean_object* v___x_297_; 
lean_dec(v_wildcardHyps_x3f_275_);
v___x_297_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object* v_wildcardHyps_x3f_298_, lean_object* v_fvarId_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(v_wildcardHyps_x3f_298_, v_fvarId_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_318_, uint8_t v___y_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 1)
{
lean_object* v_pre_321_; 
v_pre_321_ = lean_ctor_get(v_x_320_, 0);
switch(lean_obj_tag(v_pre_321_))
{
case 1:
{
lean_object* v_pre_322_; 
v_pre_322_ = lean_ctor_get(v_pre_321_, 0);
switch(lean_obj_tag(v_pre_322_))
{
case 0:
{
lean_object* v_str_323_; lean_object* v_str_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_str_323_ = lean_ctor_get(v_x_320_, 1);
v_str_324_ = lean_ctor_get(v_pre_321_, 1);
v___x_325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_326_ = lean_string_dec_eq(v_str_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_328_ = lean_string_dec_eq(v_str_324_, v___x_327_);
if (v___x_328_ == 0)
{
return v___x_328_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_330_ = lean_string_dec_eq(v_str_323_, v___x_329_);
if (v___x_330_ == 0)
{
return v___x_330_;
}
else
{
return v_suppressElabErrors_318_;
}
}
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_332_ = lean_string_dec_eq(v_str_323_, v___x_331_);
if (v___x_332_ == 0)
{
return v___x_332_;
}
else
{
return v_suppressElabErrors_318_;
}
}
}
case 1:
{
lean_object* v_pre_333_; 
v_pre_333_ = lean_ctor_get(v_pre_322_, 0);
if (lean_obj_tag(v_pre_333_) == 0)
{
lean_object* v_str_334_; lean_object* v_str_335_; lean_object* v_str_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_str_334_ = lean_ctor_get(v_x_320_, 1);
v_str_335_ = lean_ctor_get(v_pre_321_, 1);
v_str_336_ = lean_ctor_get(v_pre_322_, 1);
v___x_337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_338_ = lean_string_dec_eq(v_str_336_, v___x_337_);
if (v___x_338_ == 0)
{
return v___x_338_;
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_340_ = lean_string_dec_eq(v_str_335_, v___x_339_);
if (v___x_340_ == 0)
{
return v___x_340_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6));
v___x_342_ = lean_string_dec_eq(v_str_334_, v___x_341_);
if (v___x_342_ == 0)
{
return v___x_342_;
}
else
{
return v_suppressElabErrors_318_;
}
}
}
}
else
{
return v___y_319_;
}
}
default: 
{
return v___y_319_;
}
}
}
case 0:
{
lean_object* v_str_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_str_343_ = lean_ctor_get(v_x_320_, 1);
v___x_344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7));
v___x_345_ = lean_string_dec_eq(v_str_343_, v___x_344_);
if (v___x_345_ == 0)
{
return v___x_345_;
}
else
{
return v_suppressElabErrors_318_;
}
}
default: 
{
return v___y_319_;
}
}
}
else
{
return v___y_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_346_, lean_object* v___y_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_suppressElabErrors_boxed_349_; uint8_t v___y_7511__boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_suppressElabErrors_boxed_349_ = lean_unbox(v_suppressElabErrors_346_);
v___y_7511__boxed_350_ = lean_unbox(v___y_347_);
v_res_351_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_349_, v___y_7511__boxed_350_, v_x_348_);
lean_dec(v_x_348_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(lean_object* v_ref_354_, lean_object* v_msgData_355_, uint8_t v_severity_356_, uint8_t v_isSilent_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___y_364_; uint8_t v___y_365_; lean_object* v___y_366_; uint8_t v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___y_402_; uint8_t v___y_403_; uint8_t v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_426_; uint8_t v___y_427_; uint8_t v___y_428_; uint8_t v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; uint8_t v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; uint8_t v___x_446_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; uint8_t v___y_453_; uint8_t v___y_455_; uint8_t v___x_469_; 
v___x_446_ = 2;
v___x_469_ = l_Lean_instBEqMessageSeverity_beq(v_severity_356_, v___x_446_);
if (v___x_469_ == 0)
{
v___y_455_ = v___x_469_;
goto v___jp_454_;
}
else
{
uint8_t v___x_470_; 
lean_inc_ref(v_msgData_355_);
v___x_470_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_355_);
v___y_455_ = v___x_470_;
goto v___jp_454_;
}
v___jp_363_:
{
lean_object* v___x_373_; lean_object* v_currNamespace_374_; lean_object* v_openDecls_375_; lean_object* v_env_376_; lean_object* v_nextMacroScope_377_; lean_object* v_ngen_378_; lean_object* v_auxDeclNGen_379_; lean_object* v_traceState_380_; lean_object* v_cache_381_; lean_object* v_messages_382_; lean_object* v_infoState_383_; lean_object* v_snapshotTasks_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_398_; 
v___x_373_ = lean_st_ref_take(v___y_372_);
v_currNamespace_374_ = lean_ctor_get(v___y_371_, 5);
v_openDecls_375_ = lean_ctor_get(v___y_371_, 6);
v_env_376_ = lean_ctor_get(v___x_373_, 0);
v_nextMacroScope_377_ = lean_ctor_get(v___x_373_, 1);
v_ngen_378_ = lean_ctor_get(v___x_373_, 2);
v_auxDeclNGen_379_ = lean_ctor_get(v___x_373_, 3);
v_traceState_380_ = lean_ctor_get(v___x_373_, 4);
v_cache_381_ = lean_ctor_get(v___x_373_, 5);
v_messages_382_ = lean_ctor_get(v___x_373_, 6);
v_infoState_383_ = lean_ctor_get(v___x_373_, 7);
v_snapshotTasks_384_ = lean_ctor_get(v___x_373_, 8);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_398_ == 0)
{
v___x_386_ = v___x_373_;
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snapshotTasks_384_);
lean_inc(v_infoState_383_);
lean_inc(v_messages_382_);
lean_inc(v_cache_381_);
lean_inc(v_traceState_380_);
lean_inc(v_auxDeclNGen_379_);
lean_inc(v_ngen_378_);
lean_inc(v_nextMacroScope_377_);
lean_inc(v_env_376_);
lean_dec(v___x_373_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
lean_inc(v_openDecls_375_);
lean_inc(v_currNamespace_374_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_currNamespace_374_);
lean_ctor_set(v___x_388_, 1, v_openDecls_375_);
v___x_389_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___y_366_);
lean_inc_ref(v___y_370_);
lean_inc_ref(v___y_369_);
v___x_390_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_390_, 0, v___y_369_);
lean_ctor_set(v___x_390_, 1, v___y_368_);
lean_ctor_set(v___x_390_, 2, v___y_364_);
lean_ctor_set(v___x_390_, 3, v___y_370_);
lean_ctor_set(v___x_390_, 4, v___x_389_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*5, v___y_367_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*5 + 1, v___y_365_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*5 + 2, v_isSilent_357_);
v___x_391_ = l_Lean_MessageLog_add(v___x_390_, v_messages_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 6, v___x_391_);
v___x_393_ = v___x_386_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_env_376_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_nextMacroScope_377_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_ngen_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_auxDeclNGen_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_traceState_380_);
lean_ctor_set(v_reuseFailAlloc_397_, 5, v_cache_381_);
lean_ctor_set(v_reuseFailAlloc_397_, 6, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_397_, 7, v_infoState_383_);
lean_ctor_set(v_reuseFailAlloc_397_, 8, v_snapshotTasks_384_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_st_ref_put(v___y_372_, v___x_393_);
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
}
v___jp_399_:
{
lean_object* v_fileName_407_; lean_object* v_fileMap_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_424_; 
v_fileName_407_ = lean_ctor_get(v___y_405_, 0);
v_fileMap_408_ = lean_ctor_get(v___y_405_, 1);
v___x_409_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_355_);
v___x_410_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v___x_409_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_424_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_424_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_424_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_inc_ref_n(v_fileMap_408_, 2);
v___x_415_ = l_Lean_FileMap_toPosition(v_fileMap_408_, v___y_401_);
lean_dec(v___y_401_);
v___x_416_ = l_Lean_FileMap_toPosition(v_fileMap_408_, v___y_406_);
lean_dec(v___y_406_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0));
if (v___y_404_ == 0)
{
lean_del_object(v___x_413_);
lean_dec_ref(v___y_400_);
v___y_364_ = v___x_417_;
v___y_365_ = v___y_402_;
v___y_366_ = v_a_411_;
v___y_367_ = v___y_403_;
v___y_368_ = v___x_415_;
v___y_369_ = v_fileName_407_;
v___y_370_ = v___x_418_;
v___y_371_ = v___y_360_;
v___y_372_ = v___y_361_;
goto v___jp_363_;
}
else
{
uint8_t v___x_419_; 
lean_inc(v_a_411_);
v___x_419_ = l_Lean_MessageData_hasTag(v___y_400_, v_a_411_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_dec_ref_known(v___x_417_, 1);
lean_dec_ref(v___x_415_);
lean_dec(v_a_411_);
v___x_420_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_420_);
v___x_422_ = v___x_413_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_del_object(v___x_413_);
v___y_364_ = v___x_417_;
v___y_365_ = v___y_402_;
v___y_366_ = v_a_411_;
v___y_367_ = v___y_403_;
v___y_368_ = v___x_415_;
v___y_369_ = v_fileName_407_;
v___y_370_ = v___x_418_;
v___y_371_ = v___y_360_;
v___y_372_ = v___y_361_;
goto v___jp_363_;
}
}
}
}
v___jp_425_:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Syntax_getTailPos_x3f(v___y_430_, v___y_428_);
lean_dec(v___y_430_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_inc(v___y_432_);
v___y_400_ = v___y_426_;
v___y_401_ = v___y_432_;
v___y_402_ = v___y_427_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_429_;
v___y_405_ = v___y_431_;
v___y_406_ = v___y_432_;
goto v___jp_399_;
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_433_, 1);
v___y_400_ = v___y_426_;
v___y_401_ = v___y_432_;
v___y_402_ = v___y_427_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_429_;
v___y_405_ = v___y_431_;
v___y_406_ = v_val_434_;
goto v___jp_399_;
}
}
v___jp_435_:
{
lean_object* v_ref_442_; lean_object* v___x_443_; 
v_ref_442_ = l_Lean_replaceRef(v_ref_354_, v___y_437_);
v___x_443_ = l_Lean_Syntax_getPos_x3f(v_ref_442_, v___y_438_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___y_426_ = v___y_436_;
v___y_427_ = v___y_441_;
v___y_428_ = v___y_438_;
v___y_429_ = v___y_439_;
v___y_430_ = v_ref_442_;
v___y_431_ = v___y_440_;
v___y_432_ = v___x_444_;
goto v___jp_425_;
}
else
{
lean_object* v_val_445_; 
v_val_445_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_443_, 1);
v___y_426_ = v___y_436_;
v___y_427_ = v___y_441_;
v___y_428_ = v___y_438_;
v___y_429_ = v___y_439_;
v___y_430_ = v_ref_442_;
v___y_431_ = v___y_440_;
v___y_432_ = v_val_445_;
goto v___jp_425_;
}
}
v___jp_447_:
{
if (v___y_453_ == 0)
{
v___y_436_ = v___y_448_;
v___y_437_ = v___y_449_;
v___y_438_ = v___y_452_;
v___y_439_ = v___y_450_;
v___y_440_ = v___y_451_;
v___y_441_ = v_severity_356_;
goto v___jp_435_;
}
else
{
v___y_436_ = v___y_448_;
v___y_437_ = v___y_449_;
v___y_438_ = v___y_452_;
v___y_439_ = v___y_450_;
v___y_440_ = v___y_451_;
v___y_441_ = v___x_446_;
goto v___jp_435_;
}
}
v___jp_454_:
{
if (v___y_455_ == 0)
{
lean_object* v_toCold_456_; lean_object* v_options_457_; lean_object* v_ref_458_; uint8_t v_suppressElabErrors_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___f_462_; uint8_t v___x_463_; uint8_t v___x_464_; 
v_toCold_456_ = lean_ctor_get(v___y_360_, 0);
v_options_457_ = lean_ctor_get(v___y_360_, 1);
v_ref_458_ = lean_ctor_get(v___y_360_, 4);
v_suppressElabErrors_459_ = lean_ctor_get_uint8(v___y_360_, sizeof(void*)*10 + 1);
v___x_460_ = lean_box(v_suppressElabErrors_459_);
v___x_461_ = lean_box(v___y_455_);
v___f_462_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_462_, 0, v___x_460_);
lean_closure_set(v___f_462_, 1, v___x_461_);
v___x_463_ = 1;
v___x_464_ = l_Lean_instBEqMessageSeverity_beq(v_severity_356_, v___x_463_);
if (v___x_464_ == 0)
{
v___y_448_ = v___f_462_;
v___y_449_ = v_ref_458_;
v___y_450_ = v_suppressElabErrors_459_;
v___y_451_ = v_toCold_456_;
v___y_452_ = v___y_455_;
v___y_453_ = v___x_464_;
goto v___jp_447_;
}
else
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = l_Lean_warningAsError;
v___x_466_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_options_457_, v___x_465_);
v___y_448_ = v___f_462_;
v___y_449_ = v_ref_458_;
v___y_450_ = v_suppressElabErrors_459_;
v___y_451_ = v_toCold_456_;
v___y_452_ = v___y_455_;
v___y_453_ = v___x_466_;
goto v___jp_447_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec_ref(v_msgData_355_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___boxed(lean_object* v_ref_471_, lean_object* v_msgData_472_, lean_object* v_severity_473_, lean_object* v_isSilent_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v_severity_boxed_480_; uint8_t v_isSilent_boxed_481_; lean_object* v_res_482_; 
v_severity_boxed_480_ = lean_unbox(v_severity_473_);
v_isSilent_boxed_481_ = lean_unbox(v_isSilent_474_);
v_res_482_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_471_, v_msgData_472_, v_severity_boxed_480_, v_isSilent_boxed_481_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v_ref_471_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(lean_object* v_ref_483_, lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = 1;
v___x_495_ = 0;
v___x_496_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_483_, v_msgData_484_, v___x_494_, v___x_495_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3___boxed(lean_object* v_ref_497_, lean_object* v_msgData_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_ref_497_, v_msgData_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v_ref_497_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1));
v___x_513_ = l_Lean_MessageData_ofFormat(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(lean_object* v___f_514_, lean_object* v_stx_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___y_526_; lean_object* v_wildcardHyps_x3f_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v_options_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_options_573_ = lean_ctor_get(v___y_522_, 1);
v___x_574_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_575_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_options_573_, v___x_574_);
if (v___x_575_ == 0)
{
v___y_540_ = v___y_516_;
v___y_541_ = v___y_517_;
v___y_542_ = v___y_518_;
v___y_543_ = v___y_519_;
v___y_544_ = v___y_520_;
v___y_545_ = v___y_521_;
v___y_546_ = v___y_522_;
v___y_547_ = v___y_523_;
goto v___jp_539_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2);
v___x_577_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_515_, v___x_576_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_dec_ref_known(v___x_577_, 1);
v___y_540_ = v___y_516_;
v___y_541_ = v___y_517_;
v___y_542_ = v___y_518_;
v___y_543_ = v___y_519_;
v___y_544_ = v___y_520_;
v___y_545_ = v___y_521_;
v___y_546_ = v___y_522_;
v___y_547_ = v___y_523_;
goto v___jp_539_;
}
else
{
lean_dec_ref(v___f_514_);
return v___x_577_;
}
}
v___jp_525_:
{
lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___f_536_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed), 11, 1);
lean_closure_set(v___f_536_, 0, v_wildcardHyps_x3f_527_);
v___x_537_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed), 9, 0);
v___x_538_ = l_Lean_Elab_Tactic_withLocation(v___y_526_, v___f_536_, v___x_537_, v___f_514_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_526_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = l_Lean_Syntax_getArg(v_stx_515_, v___x_548_);
v___x_550_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_549_);
lean_dec(v___x_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_541_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = l_Lean_MVarId_getNondepPropHyps(v_a_552_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_a_554_);
v___y_526_ = v___x_550_;
v_wildcardHyps_x3f_527_ = v___x_555_;
v___y_528_ = v___y_540_;
v___y_529_ = v___y_541_;
v___y_530_ = v___y_542_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_544_;
v___y_533_ = v___y_545_;
v___y_534_ = v___y_546_;
v___y_535_ = v___y_547_;
goto v___jp_525_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v___f_514_);
v_a_556_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_553_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v___f_514_);
v_a_564_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_551_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_551_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
v___y_526_ = v___x_550_;
v_wildcardHyps_x3f_527_ = v___x_572_;
v___y_528_ = v___y_540_;
v___y_529_ = v___y_541_;
v___y_530_ = v___y_542_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_544_;
v___y_533_ = v___y_545_;
v___y_534_ = v___y_546_;
v___y_535_ = v___y_547_;
goto v___jp_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed(lean_object* v___f_578_, lean_object* v_stx_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(v___f_578_, v_stx_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_stx_579_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object* v_stx_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; 
v___f_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0));
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_602_, 0, v___f_601_);
lean_closure_set(v___f_602_, 1, v_stx_591_);
v___x_603_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_602_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(lean_object* v_stx_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Tactic_Cbv_evalCbv(v_stx_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object* v_00_u03b1_615_, lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_616_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object* v_00_u03b1_627_, lean_object* v_msg_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_00_u03b1_627_, v_msg_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(lean_object* v_ref_639_, lean_object* v_msgData_640_, uint8_t v_severity_641_, uint8_t v_isSilent_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_639_, v_msgData_640_, v_severity_641_, v_isSilent_642_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___boxed(lean_object* v_ref_653_, lean_object* v_msgData_654_, lean_object* v_severity_655_, lean_object* v_isSilent_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v_severity_boxed_666_; uint8_t v_isSilent_boxed_667_; lean_object* v_res_668_; 
v_severity_boxed_666_ = lean_unbox(v_severity_655_);
v_isSilent_boxed_667_ = lean_unbox(v_isSilent_656_);
v_res_668_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(v_ref_653_, v_msgData_654_, v_severity_boxed_666_, v_isSilent_boxed_667_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_ref_653_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1(){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_686_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3));
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6));
v___x_689_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___boxed), 10, 0);
v___x_690_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_686_, v___x_687_, v___x_688_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
return v_res_692_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object* v_00_u03b1_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object* v_00_u03b1_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(v_00_u03b1_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_ref_729_; lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_ref_729_ = lean_ctor_get(v___y_726_, 4);
v___x_730_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_ref_729_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_ref_729_);
lean_ctor_set(v___x_735_, 1, v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 1);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(lean_object* v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1);
v___x_757_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v___x_756_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v_x_758_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(uint8_t v___x_768_, lean_object* v___f_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___y_780_; lean_object* v___x_792_; 
v___x_792_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_771_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; uint8_t v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1));
v___x_795_ = 0;
v___x_796_ = 0;
v___x_797_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_797_, 0, v___x_795_);
lean_ctor_set_uint8(v___x_797_, 1, v___x_768_);
lean_ctor_set_uint8(v___x_797_, 2, v___x_796_);
lean_ctor_set_uint8(v___x_797_, 3, v___x_768_);
v___x_798_ = l_Lean_MVarId_applyConst(v_a_793_, v___x_794_, v___x_797_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
if (lean_obj_tag(v_a_799_) == 1)
{
lean_object* v_tail_800_; 
v_tail_800_ = lean_ctor_get(v_a_799_, 1);
if (lean_obj_tag(v_tail_800_) == 0)
{
lean_object* v_head_801_; lean_object* v___x_802_; 
lean_dec_ref(v___f_769_);
v_head_801_ = lean_ctor_get(v_a_799_, 0);
lean_inc(v_head_801_);
lean_dec_ref_known(v_a_799_, 2);
v___x_802_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_head_801_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
v___y_780_ = v___x_802_;
goto v___jp_779_;
}
else
{
lean_object* v___x_803_; 
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
v___x_803_ = lean_apply_6(v___f_769_, v_a_799_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
v___y_780_ = v___x_803_;
goto v___jp_779_;
}
}
else
{
lean_object* v___x_804_; 
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
v___x_804_ = lean_apply_6(v___f_769_, v_a_799_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
v___y_780_ = v___x_804_;
goto v___jp_779_;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v___f_769_);
v_a_805_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_798_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_798_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v___f_769_);
v_a_813_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_792_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_792_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
v___jp_779_:
{
if (lean_obj_tag(v___y_780_) == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref_known(v___y_780_, 1);
v___x_781_ = lean_box(0);
v___x_782_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_781_, v___y_771_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v___x_782_, 0);
lean_dec(v_unused_791_);
v___x_784_ = v___x_782_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_dec(v___x_782_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = lean_box(0);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
return v___x_782_;
}
}
else
{
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v___y_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(lean_object* v___x_821_, lean_object* v___f_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_1699__boxed_832_; lean_object* v_res_833_; 
v___x_1699__boxed_832_ = lean_unbox(v___x_821_);
v_res_833_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(v___x_1699__boxed_832_, v___f_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_833_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1));
v___x_838_ = l_Lean_MessageData_ofFormat(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(lean_object* v___f_839_, lean_object* v_stx_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_options_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_options_850_ = lean_ctor_get(v___y_847_, 1);
v___x_851_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_852_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_options_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_839_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2);
v___x_855_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_840_, v___x_854_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; 
lean_dec_ref_known(v___x_855_, 1);
v___x_856_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_839_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_856_;
}
else
{
lean_dec_ref(v___f_839_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(lean_object* v___f_857_, lean_object* v_stx_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(v___f_857_, v_stx_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v_stx_858_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object* v_stx_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
lean_inc(v_stx_876_);
v___x_887_ = l_Lean_Syntax_isOfKind(v_stx_876_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v_stx_876_);
v___x_888_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_888_;
}
else
{
lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; 
v___f_889_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2));
v___x_890_ = lean_box(v___x_887_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed), 11, 2);
lean_closure_set(v___f_891_, 0, v___x_890_);
lean_closure_set(v___f_891_, 1, v___f_889_);
v___f_892_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_892_, 0, v___f_891_);
lean_closure_set(v___f_892_, 1, v_stx_876_);
v___x_893_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_892_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object* v_stx_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(v_stx_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object* v_00_u03b1_905_, lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object* v_00_u03b1_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(v_00_u03b1_913_, v_msg_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1(){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_930_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
v___x_931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1));
v___x_932_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed), 10, 0);
v___x_933_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_929_, v___x_930_, v___x_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
return v_res_935_;
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
