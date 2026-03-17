// Lean compiler output
// Module: Lean.Elab.Deriving.ReflBEq
// Imports: import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util import Init.LawfulBEqTactics
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_InductiveVal_isNested(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ReflBEq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(120, 198, 190, 36, 14, 95, 233, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "DerivingHelpers"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticDeriving_ReflEq_tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52_value),LEAN_SCALAR_PTR_LITERAL(20, 45, 30, 199, 86, 148, 73, 212)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53_value),LEAN_SCALAR_PTR_LITERAL(59, 102, 201, 20, 211, 124, 83, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "deriving_ReflEq_tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reflBEq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58_value),LEAN_SCALAR_PTR_LITERAL(244, 86, 89, 238, 156, 100, 153, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Deriving `ReflBEq` for nested inductives is not supported"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Deriving `ReflBEq` for mutual inductives is not supported"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 194, 191, 195, 228, 132, 196, 101)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(168, 83, 209, 246, 44, 7, 132, 53)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 66, 189, 149, 2, 218, 35, 160)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(95, 189, 69, 16, 47, 22, 203, 145)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(9, 192, 197, 98, 93, 34, 198, 167)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 170, 107, 30, 69, 106, 9, 80)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 228, 26, 163, 2, 191, 47, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 106, 161, 213, 213, 83, 190, 134)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(3, 97, 137, 105, 223, 75, 255, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(53, 245, 46, 218, 50, 209, 251, 116)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(123, 250, 154, 0, 154, 13, 165, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 3, 181, 2, 27, 198, 42)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)(((size_t)(333339820) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 0, 136, 99, 190, 32, 15, 146)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 44, 252, 108, 226, 48, 218, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 141, 163, 178, 170, 2, 48, 48)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(108, 58, 17, 200, 161, 206, 41, 164)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_options_7_; uint8_t v_hasTrace_8_; 
v_options_7_ = lean_ctor_get(v___y_5_, 2);
v_hasTrace_8_ = lean_ctor_get_uint8(v_options_7_, sizeof(void*)*1);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_cls_4_);
v___x_9_ = lean_box(v_hasTrace_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_inheritedTraceOptions_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_inheritedTraceOptions_11_ = lean_ctor_get(v___y_5_, 13);
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___closed__1));
v___x_13_ = l_Lean_Name_append(v___x_12_, v_cls_4_);
v___x_14_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_11_, v_options_7_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg(v_cls_21_, v___y_26_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___boxed(lean_object* v_cls_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(v_cls_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3(lean_object* v_msgData_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_45_; lean_object* v_env_46_; lean_object* v___x_47_; lean_object* v_mctx_48_; lean_object* v_lctx_49_; lean_object* v_options_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_45_ = lean_st_ref_get(v___y_43_);
v_env_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref(v_env_46_);
lean_dec(v___x_45_);
v___x_47_ = lean_st_ref_get(v___y_41_);
v_mctx_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_mctx_48_);
lean_dec(v___x_47_);
v_lctx_49_ = lean_ctor_get(v___y_40_, 2);
v_options_50_ = lean_ctor_get(v___y_42_, 2);
lean_inc_ref(v_options_50_);
lean_inc_ref(v_lctx_49_);
v___x_51_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_51_, 0, v_env_46_);
lean_ctor_set(v___x_51_, 1, v_mctx_48_);
lean_ctor_set(v___x_51_, 2, v_lctx_49_);
lean_ctor_set(v___x_51_, 3, v_options_50_);
v___x_52_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v_msgData_39_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3___boxed(lean_object* v_msgData_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3(v_msgData_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; double v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_float_of_nat(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(lean_object* v_cls_66_, lean_object* v_msg_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_ref_73_; lean_object* v___x_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_119_; 
v_ref_73_ = lean_ctor_get(v___y_70_, 5);
v___x_74_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3(v_msg_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_119_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_119_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_119_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v_traceState_80_; lean_object* v_env_81_; lean_object* v_nextMacroScope_82_; lean_object* v_ngen_83_; lean_object* v_auxDeclNGen_84_; lean_object* v_cache_85_; lean_object* v_messages_86_; lean_object* v_infoState_87_; lean_object* v_snapshotTasks_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_118_; 
v___x_79_ = lean_st_ref_take(v___y_71_);
v_traceState_80_ = lean_ctor_get(v___x_79_, 4);
v_env_81_ = lean_ctor_get(v___x_79_, 0);
v_nextMacroScope_82_ = lean_ctor_get(v___x_79_, 1);
v_ngen_83_ = lean_ctor_get(v___x_79_, 2);
v_auxDeclNGen_84_ = lean_ctor_get(v___x_79_, 3);
v_cache_85_ = lean_ctor_get(v___x_79_, 5);
v_messages_86_ = lean_ctor_get(v___x_79_, 6);
v_infoState_87_ = lean_ctor_get(v___x_79_, 7);
v_snapshotTasks_88_ = lean_ctor_get(v___x_79_, 8);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_118_ == 0)
{
v___x_90_ = v___x_79_;
v_isShared_91_ = v_isSharedCheck_118_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_snapshotTasks_88_);
lean_inc(v_infoState_87_);
lean_inc(v_messages_86_);
lean_inc(v_cache_85_);
lean_inc(v_traceState_80_);
lean_inc(v_auxDeclNGen_84_);
lean_inc(v_ngen_83_);
lean_inc(v_nextMacroScope_82_);
lean_inc(v_env_81_);
lean_dec(v___x_79_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_118_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint64_t v_tid_92_; lean_object* v_traces_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_117_; 
v_tid_92_ = lean_ctor_get_uint64(v_traceState_80_, sizeof(void*)*1);
v_traces_93_ = lean_ctor_get(v_traceState_80_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_traceState_80_);
if (v_isSharedCheck_117_ == 0)
{
v___x_95_ = v_traceState_80_;
v_isShared_96_ = v_isSharedCheck_117_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_traces_93_);
lean_dec(v_traceState_80_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_117_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; double v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_97_ = lean_box(0);
v___x_98_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__0);
v___x_99_ = 0;
v___x_100_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__1));
v___x_101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_101_, 0, v_cls_66_);
lean_ctor_set(v___x_101_, 1, v___x_97_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set_float(v___x_101_, sizeof(void*)*3, v___x_98_);
lean_ctor_set_float(v___x_101_, sizeof(void*)*3 + 8, v___x_98_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 16, v___x_99_);
v___x_102_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___closed__2));
v___x_103_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v_a_75_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_inc(v_ref_73_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_73_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l_Lean_PersistentArray_push___redArg(v_traces_93_, v___x_104_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_105_);
v___x_107_ = v___x_95_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_105_);
lean_ctor_set_uint64(v_reuseFailAlloc_116_, sizeof(void*)*1, v_tid_92_);
v___x_107_ = v_reuseFailAlloc_116_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 4, v___x_107_);
v___x_109_ = v___x_90_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_env_81_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_nextMacroScope_82_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_ngen_83_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v_auxDeclNGen_84_);
lean_ctor_set(v_reuseFailAlloc_115_, 4, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_115_, 5, v_cache_85_);
lean_ctor_set(v_reuseFailAlloc_115_, 6, v_messages_86_);
lean_ctor_set(v_reuseFailAlloc_115_, 7, v_infoState_87_);
lean_ctor_set(v_reuseFailAlloc_115_, 8, v_snapshotTasks_88_);
v___x_109_ = v_reuseFailAlloc_115_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_110_ = lean_st_ref_set(v___y_71_, v___x_109_);
v___x_111_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_111_);
v___x_113_ = v___x_77_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___boxed(lean_object* v_cls_120_, lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_cls_120_, v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_box(1);
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__2));
v___x_134_ = l_Lean_MessageData_ofFormat(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
return v_x_135_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_160_; 
v_head_137_ = lean_ctor_get(v_x_136_, 0);
v_tail_138_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_160_ == 0)
{
v___x_140_ = v_x_136_;
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_tail_138_);
lean_inc(v_head_137_);
lean_dec(v_x_136_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_before_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_158_; 
v_before_142_ = lean_ctor_get(v_head_137_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_head_137_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_head_137_, 1);
lean_dec(v_unused_159_);
v___x_144_ = v_head_137_;
v_isShared_145_ = v_isSharedCheck_158_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_before_142_);
lean_dec(v_head_137_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_158_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 7);
lean_ctor_set(v___x_144_, 1, v___x_146_);
lean_ctor_set(v___x_144_, 0, v_x_135_);
v___x_148_ = v___x_144_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_x_135_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_157_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__3);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 7);
lean_ctor_set(v___x_140_, 1, v___x_149_);
lean_ctor_set(v___x_140_, 0, v___x_148_);
v___x_151_ = v___x_140_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = l_Lean_MessageData_ofSyntax(v_before_142_);
v___x_153_ = l_Lean_indentD(v___x_152_);
v___x_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_151_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v_x_135_ = v___x_154_;
v_x_136_ = v_tail_138_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__6(lean_object* v_opts_161_, lean_object* v_opt_162_){
_start:
{
lean_object* v_name_163_; lean_object* v_defValue_164_; lean_object* v_map_165_; lean_object* v___x_166_; 
v_name_163_ = lean_ctor_get(v_opt_162_, 0);
v_defValue_164_ = lean_ctor_get(v_opt_162_, 1);
v_map_165_ = lean_ctor_get(v_opts_161_, 0);
v___x_166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_165_, v_name_163_);
if (lean_obj_tag(v___x_166_) == 0)
{
uint8_t v___x_167_; 
v___x_167_ = lean_unbox(v_defValue_164_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; 
v_val_168_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v___x_166_);
if (lean_obj_tag(v_val_168_) == 1)
{
uint8_t v_v_169_; 
v_v_169_ = lean_ctor_get_uint8(v_val_168_, 0);
lean_dec_ref(v_val_168_);
return v_v_169_;
}
else
{
uint8_t v___x_170_; 
lean_dec(v_val_168_);
v___x_170_ = lean_unbox(v_defValue_164_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__6___boxed(lean_object* v_opts_171_, lean_object* v_opt_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__6(v_opts_171_, v_opt_172_);
lean_dec_ref(v_opt_172_);
lean_dec_ref(v_opts_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__1));
v___x_179_ = l_Lean_MessageData_ofFormat(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg(lean_object* v_msgData_180_, lean_object* v_macroStack_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_options_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_options_184_ = lean_ctor_get(v___y_182_, 2);
v___x_185_ = l_Lean_Elab_pp_macroStack;
v___x_186_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__6(v_options_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec(v_macroStack_181_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v_msgData_180_);
return v___x_187_;
}
else
{
if (lean_obj_tag(v_macroStack_181_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_msgData_180_);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_after_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_205_; 
v_head_189_ = lean_ctor_get(v_macroStack_181_, 0);
lean_inc(v_head_189_);
v_after_190_ = lean_ctor_get(v_head_189_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_head_189_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_head_189_, 0);
lean_dec(v_unused_206_);
v___x_192_ = v_head_189_;
v_isShared_193_ = v_isSharedCheck_205_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_after_190_);
lean_dec(v_head_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_205_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7___closed__0);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 7);
lean_ctor_set(v___x_192_, 1, v___x_194_);
lean_ctor_set(v___x_192_, 0, v_msgData_180_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_msgData_180_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_204_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_msgData_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_197_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___closed__2);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_MessageData_ofSyntax(v_after_190_);
v___x_200_ = l_Lean_indentD(v___x_199_);
v_msgData_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_201_, 0, v___x_198_);
lean_ctor_set(v_msgData_201_, 1, v___x_200_);
v___x_202_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5_spec__7(v_msgData_201_, v_macroStack_181_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg___boxed(lean_object* v_msgData_207_, lean_object* v_macroStack_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg(v_msgData_207_, v_macroStack_208_, v___y_209_);
lean_dec_ref(v___y_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v_a_222_; lean_object* v_macroStack_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_ref_220_ = lean_ctor_get(v___y_217_, 5);
v___x_221_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__3(v_msg_212_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_221_);
v_macroStack_223_ = lean_ctor_get(v___y_213_, 1);
lean_inc(v_macroStack_223_);
lean_dec_ref(v___y_213_);
lean_inc(v_macroStack_223_);
v___x_224_ = l_Lean_Elab_getBetterRef(v_ref_220_, v_macroStack_223_);
v___x_225_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg(v_a_222_, v_macroStack_223_, v___y_217_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_224_);
lean_ctor_set(v___x_230_, 1, v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 1);
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg___boxed(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
return v_res_243_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(lean_object* v_constName_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_env_259_; lean_object* v___x_260_; 
v___x_258_ = lean_st_ref_get(v___y_256_);
v_env_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_258_);
lean_inc(v_constName_250_);
v___x_260_ = l_Lean_isInductiveCore_x3f(v_env_259_, v_constName_250_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_261_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1);
v___x_262_ = 0;
v___x_263_ = l_Lean_MessageData_ofConstName(v_constName_250_, v___x_262_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_261_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(v___x_266_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
return v___x_267_;
}
else
{
lean_object* v_val_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v___y_251_);
lean_dec(v_constName_250_);
v_val_268_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_260_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_val_268_);
lean_dec(v___x_260_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 0);
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_val_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___boxed(lean_object* v_constName_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_constName_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
if (lean_obj_tag(v_a_285_) == 0)
{
lean_object* v___x_287_; 
v___x_287_ = l_List_reverse___redArg(v_a_286_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v_tail_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_298_; 
v_head_288_ = lean_ctor_get(v_a_285_, 0);
v_tail_289_ = lean_ctor_get(v_a_285_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_285_);
if (v_isSharedCheck_298_ == 0)
{
v___x_291_ = v_a_285_;
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_tail_289_);
lean_inc(v_head_288_);
lean_dec(v_a_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = l_Lean_MessageData_ofSyntax(v_head_288_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_a_286_);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_a_286_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_285_ = v_tail_289_;
v_a_286_ = v___x_295_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3));
v___x_315_ = l_Lean_mkCIdent(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Array_mkArray0(lean_box(0));
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36));
v___x_385_ = l_String_toRawSubstring_x27(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(lean_object* v_declName_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
lean_inc_ref(v_a_444_);
v___x_451_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_declName_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v_all_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_451_);
v_all_617_ = lean_ctor_get(v_a_452_, 3);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = l_List_lengthTR___redArg(v_all_617_);
v___x_620_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
v___y_600_ = v_a_444_;
v___y_601_ = v_a_445_;
v___y_602_ = v_a_446_;
v___y_603_ = v_a_447_;
v___y_604_ = v_a_448_;
v___y_605_ = v_a_449_;
goto v___jp_599_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_452_);
v___x_621_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65);
v___x_622_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(v___x_621_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
v___jp_453_:
{
lean_object* v___x_460_; 
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v_a_452_);
v___x_460_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_452_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref(v___x_460_);
lean_inc(v_a_461_);
v___x_462_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_461_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1));
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v_a_461_);
lean_inc(v_a_452_);
v___x_465_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_464_, v_a_452_, v_a_461_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3));
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc(v_a_461_);
lean_inc(v_a_452_);
v___x_468_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_467_, v_a_452_, v_a_461_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v___x_470_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_452_, v_a_461_, v___y_458_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v_ref_472_; lean_object* v_quotContext_473_; lean_object* v_currMacroScope_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_574_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref(v___x_470_);
v_ref_472_ = lean_ctor_get(v___y_458_, 5);
v_quotContext_473_ = lean_ctor_get(v___y_458_, 10);
v_currMacroScope_474_ = lean_ctor_get(v___y_458_, 11);
v___x_475_ = l_Array_append___redArg(v_a_463_, v_a_466_);
lean_dec(v_a_466_);
v___x_476_ = l_Array_append___redArg(v___x_475_, v_a_469_);
lean_dec(v_a_469_);
v___x_477_ = 0;
v___x_478_ = l_Lean_SourceInfo_fromRef(v_ref_472_, v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8));
v___x_480_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9);
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11));
lean_inc(v___x_478_);
v___x_482_ = l_Lean_Syntax_node1(v___x_478_, v___x_481_, v_a_471_);
lean_inc(v___x_478_);
v___x_483_ = l_Lean_Syntax_node2(v___x_478_, v___x_479_, v___x_480_, v___x_482_);
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14));
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16));
v___x_486_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17);
lean_inc(v___x_478_);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v___x_478_);
lean_ctor_set(v___x_487_, 1, v___x_481_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
lean_inc_ref_n(v___x_487_, 7);
lean_inc(v___x_478_);
v___x_488_ = l_Lean_Syntax_node7(v___x_478_, v___x_485_, v___x_487_, v___x_487_, v___x_487_, v___x_487_, v___x_487_, v___x_487_, v___x_487_);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18));
v___x_490_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19));
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21));
lean_inc_ref(v___x_487_);
lean_inc(v___x_478_);
v___x_492_ = l_Lean_Syntax_node1(v___x_478_, v___x_491_, v___x_487_);
lean_inc(v___x_478_);
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_478_);
lean_ctor_set(v___x_493_, 1, v___x_489_);
v___x_494_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23));
v___x_495_ = l_Array_append___redArg(v___x_486_, v___x_476_);
lean_dec_ref(v___x_476_);
lean_inc(v___x_478_);
v___x_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_496_, 0, v___x_478_);
lean_ctor_set(v___x_496_, 1, v___x_481_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v___x_497_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25));
v___x_498_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26));
lean_inc(v___x_478_);
v___x_499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_478_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
lean_inc(v___x_478_);
v___x_500_ = l_Lean_Syntax_node2(v___x_478_, v___x_497_, v___x_499_, v___x_483_);
lean_inc(v___x_478_);
v___x_501_ = l_Lean_Syntax_node2(v___x_478_, v___x_494_, v___x_496_, v___x_500_);
v___x_502_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28));
v___x_503_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29));
lean_inc(v___x_478_);
v___x_504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_478_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31));
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33));
v___x_507_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35));
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37);
v___x_509_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38));
lean_inc(v_currMacroScope_474_);
lean_inc(v_quotContext_473_);
v___x_510_ = l_Lean_addMacroScope(v_quotContext_473_, v___x_509_, v_currMacroScope_474_);
v___x_511_ = lean_box(0);
v___x_512_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40));
lean_inc(v___x_478_);
v___x_513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_513_, 0, v___x_478_);
lean_ctor_set(v___x_513_, 1, v___x_508_);
lean_ctor_set(v___x_513_, 2, v___x_510_);
lean_ctor_set(v___x_513_, 3, v___x_512_);
lean_inc_ref(v___x_487_);
lean_inc(v___x_478_);
v___x_514_ = l_Lean_Syntax_node2(v___x_478_, v___x_507_, v___x_513_, v___x_487_);
v___x_515_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42));
v___x_516_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43));
lean_inc(v___x_478_);
v___x_517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_478_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45));
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46));
lean_inc(v___x_478_);
v___x_520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_478_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49));
v___x_522_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51));
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54));
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55));
lean_inc(v___x_478_);
v___x_525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_478_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_inc(v___x_478_);
v___x_526_ = l_Lean_Syntax_node1(v___x_478_, v___x_523_, v___x_525_);
lean_inc(v___x_478_);
v___x_527_ = l_Lean_Syntax_node1(v___x_478_, v___x_481_, v___x_526_);
lean_inc(v___x_478_);
v___x_528_ = l_Lean_Syntax_node1(v___x_478_, v___x_522_, v___x_527_);
lean_inc(v___x_478_);
v___x_529_ = l_Lean_Syntax_node1(v___x_478_, v___x_521_, v___x_528_);
lean_inc(v___x_478_);
v___x_530_ = l_Lean_Syntax_node2(v___x_478_, v___x_518_, v___x_520_, v___x_529_);
lean_inc_ref(v___x_487_);
lean_inc(v___x_478_);
v___x_531_ = l_Lean_Syntax_node3(v___x_478_, v___x_515_, v___x_517_, v___x_487_, v___x_530_);
lean_inc_ref_n(v___x_487_, 2);
lean_inc(v___x_478_);
v___x_532_ = l_Lean_Syntax_node3(v___x_478_, v___x_481_, v___x_487_, v___x_487_, v___x_531_);
lean_inc(v___x_478_);
v___x_533_ = l_Lean_Syntax_node2(v___x_478_, v___x_506_, v___x_514_, v___x_532_);
lean_inc(v___x_478_);
v___x_534_ = l_Lean_Syntax_node1(v___x_478_, v___x_481_, v___x_533_);
lean_inc(v___x_478_);
v___x_535_ = l_Lean_Syntax_node1(v___x_478_, v___x_505_, v___x_534_);
lean_inc_ref(v___x_487_);
lean_inc(v___x_478_);
v___x_536_ = l_Lean_Syntax_node3(v___x_478_, v___x_502_, v___x_504_, v___x_535_, v___x_487_);
lean_inc_ref(v___x_487_);
lean_inc(v___x_478_);
v___x_537_ = l_Lean_Syntax_node6(v___x_478_, v___x_490_, v___x_492_, v___x_493_, v___x_487_, v___x_487_, v___x_501_, v___x_536_);
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_539_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1___redArg(v___x_538_, v___y_458_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_574_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_574_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_574_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_544_ = l_Lean_Syntax_node2(v___x_478_, v___x_484_, v___x_488_, v___x_537_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_mk_empty_array_with_capacity(v___x_545_);
v___x_547_ = lean_array_push(v___x_546_, v___x_544_);
v___x_548_ = lean_unbox(v_a_540_);
lean_dec(v_a_540_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_547_);
v___x_550_ = v___x_542_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_547_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_del_object(v___x_542_);
v___x_552_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61);
lean_inc_ref(v___x_547_);
v___x_553_ = lean_array_to_list(v___x_547_);
v___x_554_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(v___x_553_, v___x_511_);
v___x_555_ = l_Lean_MessageData_ofList(v___x_554_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_552_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_538_, v___x_556_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_557_, 0);
lean_dec(v_unused_565_);
v___x_559_ = v___x_557_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_dec(v___x_557_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_547_);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_547_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v___x_547_);
v_a_566_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_557_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_557_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_a_469_);
lean_dec(v_a_466_);
lean_dec(v_a_463_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
v_a_575_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_470_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_470_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_dec(v_a_466_);
lean_dec(v_a_463_);
lean_dec(v_a_461_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_a_452_);
return v___x_468_;
}
}
else
{
lean_dec(v_a_463_);
lean_dec(v_a_461_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_a_452_);
return v___x_465_;
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_a_461_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_a_452_);
v_a_583_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_462_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_462_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_a_452_);
v_a_591_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_460_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_460_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
v___jp_599_:
{
uint8_t v___x_606_; 
v___x_606_ = l_Lean_InductiveVal_isNested(v_a_452_);
if (v___x_606_ == 0)
{
v___y_454_ = v___y_600_;
v___y_455_ = v___y_601_;
v___y_456_ = v___y_602_;
v___y_457_ = v___y_603_;
v___y_458_ = v___y_604_;
v___y_459_ = v___y_605_;
goto v___jp_453_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_452_);
v___x_607_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63);
v___x_608_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(v___x_607_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
v_a_631_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_451_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_451_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed(lean_object* v_declName_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(v_declName_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(lean_object* v_cls_648_, lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_cls_648_, v_msg_649_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___boxed(lean_object* v_cls_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(v_cls_658_, v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4(lean_object* v_00_u03b1_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___redArg(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4___boxed(lean_object* v_00_u03b1_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4(v_00_u03b1_678_, v_msg_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5(lean_object* v_msgData_688_, lean_object* v_macroStack_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___redArg(v_msgData_688_, v_macroStack_689_, v___y_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5___boxed(lean_object* v_msgData_698_, lean_object* v_macroStack_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__4_spec__5(v_msgData_698_, v_macroStack_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(lean_object* v_as_708_, size_t v_i_709_, size_t v_stop_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_eq(v_i_709_, v_stop_710_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_array_uget_borrowed(v_as_708_, v_i_709_);
lean_inc(v___y_713_);
lean_inc_ref(v___y_712_);
lean_inc(v___x_716_);
v___x_717_ = l_Lean_Elab_Command_elabCommand(v___x_716_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; size_t v___x_719_; size_t v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_i_709_, v___x_719_);
v_i_709_ = v___x_720_;
v_b_711_ = v_a_718_;
goto _start;
}
else
{
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v___x_717_;
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_b_711_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0___boxed(lean_object* v_as_723_, lean_object* v_i_724_, lean_object* v_stop_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
size_t v_i_boxed_730_; size_t v_stop_boxed_731_; lean_object* v_res_732_; 
v_i_boxed_730_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_stop_boxed_731_ = lean_unbox_usize(v_stop_725_);
lean_dec(v_stop_725_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_as_723_, v_i_boxed_730_, v_stop_boxed_731_, v_b_726_, v___y_727_, v___y_728_);
lean_dec_ref(v_as_723_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(lean_object* v___x_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
lean_inc_ref(v___y_734_);
v___x_737_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_759_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_759_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_759_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_759_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_array_get_size(v_a_738_);
v___x_744_ = lean_box(0);
v___x_745_ = lean_nat_dec_lt(v___x_742_, v___x_743_);
if (v___x_745_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_a_738_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_747_ = v___x_740_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_744_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
uint8_t v___x_749_; 
v___x_749_ = lean_nat_dec_le(v___x_743_, v___x_743_);
if (v___x_749_ == 0)
{
if (v___x_745_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v_a_738_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_751_ = v___x_740_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_744_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_740_);
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_743_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_738_, v___x_753_, v___x_754_, v___x_744_, v___y_734_, v___y_735_);
lean_dec(v_a_738_);
return v___x_755_;
}
}
else
{
size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
lean_del_object(v___x_740_);
v___x_756_ = ((size_t)0ULL);
v___x_757_ = lean_usize_of_nat(v___x_743_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_738_, v___x_756_, v___x_757_, v___x_744_, v___y_734_, v___y_735_);
lean_dec(v_a_738_);
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
v_a_760_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_737_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_737_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed(lean_object* v___x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(v___x_768_, v___y_769_, v___y_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(lean_object* v_declName_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
lean_inc(v_declName_773_);
v___x_777_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_777_, 0, v_declName_773_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(v___f_778_, 0, v___x_777_);
v___x_779_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_773_, v___f_778_, v_a_774_, v_a_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___boxed(lean_object* v_declName_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_declName_780_, v_a_781_, v_a_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; lean_object* v_env_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_788_ = lean_st_ref_get(v___y_786_);
v_env_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc_ref(v_env_789_);
lean_dec(v___x_788_);
v___x_790_ = l_Lean_isInductiveCore(v_env_789_, v_declName_785_);
v___x_791_ = lean_box(v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_793_, v___y_794_);
lean_dec(v___y_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(lean_object* v_declName_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_797_, v___y_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(v_declName_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(uint8_t v_____do__lift_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
if (v_____do__lift_807_ == 0)
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = 1;
v___x_812_ = lean_box(v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
else
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = 0;
v___x_815_ = lean_box(v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
uint8_t v_____do__lift_2065__boxed_821_; lean_object* v_res_822_; 
v_____do__lift_2065__boxed_821_ = lean_unbox(v_____do__lift_817_);
v_res_822_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v_____do__lift_2065__boxed_821_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(lean_object* v_as_823_, size_t v_i_824_, size_t v_stop_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_usize_dec_eq(v_i_824_, v_stop_825_);
if (v___x_829_ == 0)
{
uint8_t v___x_830_; uint8_t v_a_832_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_830_ = 1;
v___x_838_ = lean_array_uget_borrowed(v_as_823_, v_i_824_);
lean_inc(v___x_838_);
v___x_839_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v___x_838_, v___y_827_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint8_t v___x_844_; 
v___x_844_ = lean_unbox(v_a_840_);
lean_dec(v_a_840_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_box(v___x_830_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
else
{
lean_del_object(v___x_842_);
v_a_832_ = v___x_829_;
goto v___jp_831_;
}
}
}
else
{
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_850_; uint8_t v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_839_);
v___x_851_ = lean_unbox(v_a_850_);
lean_dec(v_a_850_);
v_a_832_ = v___x_851_;
goto v___jp_831_;
}
else
{
return v___x_839_;
}
}
v___jp_831_:
{
if (v_a_832_ == 0)
{
size_t v___x_833_; size_t v___x_834_; 
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_add(v_i_824_, v___x_833_);
v_i_824_ = v___x_834_;
goto _start;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(v___x_830_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
}
else
{
uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = 0;
v___x_853_ = lean_box(v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2___boxed(lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
size_t v_i_boxed_861_; size_t v_stop_boxed_862_; lean_object* v_res_863_; 
v_i_boxed_861_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_862_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_as_855_, v_i_boxed_861_, v_stop_boxed_862_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_as_855_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(lean_object* v_as_864_, size_t v_sz_865_, size_t v_i_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = lean_usize_dec_lt(v_i_866_, v_sz_865_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_b_867_);
return v___x_872_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; 
v_a_873_ = lean_array_uget_borrowed(v_as_864_, v_i_866_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v_a_873_);
v___x_874_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_a_873_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; size_t v___x_876_; size_t v___x_877_; 
lean_dec_ref(v___x_874_);
v___x_875_ = lean_box(0);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_866_, v___x_876_);
v_i_866_ = v___x_877_;
v_b_867_ = v___x_875_;
goto _start;
}
else
{
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0___boxed(lean_object* v_as_879_, lean_object* v_sz_880_, lean_object* v_i_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
size_t v_sz_boxed_886_; size_t v_i_boxed_887_; lean_object* v_res_888_; 
v_sz_boxed_886_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v_i_boxed_887_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_as_879_, v_sz_boxed_886_, v_i_boxed_887_, v_b_882_, v___y_883_, v___y_884_);
lean_dec_ref(v_as_879_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(lean_object* v_declNames_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___y_917_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_array_get_size(v_declNames_889_);
v___x_922_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_922_, v_a_890_, v_a_891_);
v___y_917_ = v___x_923_;
goto v___jp_916_;
}
else
{
if (v___x_922_ == 0)
{
goto v___jp_893_;
}
else
{
size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((size_t)0ULL);
v___x_925_ = lean_usize_of_nat(v___x_921_);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_declNames_889_, v___x_924_, v___x_925_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; uint8_t v___x_928_; lean_object* v___x_929_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = lean_unbox(v_a_927_);
lean_dec(v_a_927_);
v___x_929_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_928_, v_a_890_, v_a_891_);
v___y_917_ = v___x_929_;
goto v___jp_916_;
}
else
{
v___y_917_ = v___x_926_;
goto v___jp_916_;
}
}
}
v___jp_893_:
{
lean_object* v___x_894_; size_t v_sz_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_894_ = lean_box(0);
v_sz_895_ = lean_array_size(v_declNames_889_);
v___x_896_ = ((size_t)0ULL);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_declNames_889_, v_sz_895_, v___x_896_, v___x_894_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_906_; 
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v___x_897_, 0);
lean_dec(v_unused_907_);
v___x_899_ = v___x_897_;
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
else
{
lean_dec(v___x_897_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_901_ = 1;
v___x_902_ = lean_box(v___x_901_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_897_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_897_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
v___jp_916_:
{
if (lean_obj_tag(v___y_917_) == 0)
{
lean_object* v_a_918_; uint8_t v___x_919_; 
v_a_918_ = lean_ctor_get(v___y_917_, 0);
v___x_919_ = lean_unbox(v_a_918_);
if (v___x_919_ == 0)
{
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v___y_917_;
}
else
{
lean_dec_ref(v___y_917_);
goto v___jp_893_;
}
}
else
{
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v___y_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed(lean_object* v_declNames_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(v_declNames_930_, v_a_931_, v_a_932_);
lean_dec_ref(v_declNames_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3));
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_));
v___x_1004_ = l_Lean_Elab_registerDerivingHandler(v___x_1002_, v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___x_1004_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_1006_ = 0;
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_));
v___x_1008_ = l_Lean_registerTraceClass(v___x_1005_, v___x_1006_, v___x_1007_);
return v___x_1008_;
}
else
{
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2____boxed(lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
return v_res_1010_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_ReflBEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_ReflBEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_ReflBEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_ReflBEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_ReflBEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_ReflBEq(builtin);
}
#ifdef __cplusplus
}
#endif
