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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ReflBEq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(120, 198, 190, 36, 14, 95, 233, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Deriving `ReflBEq` for nested inductives is not supported"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Deriving `ReflBEq` for mutual inductives is not supported"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67 = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(157, 194, 191, 195, 228, 132, 196, 101)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(168, 83, 209, 246, 44, 7, 132, 53)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 66, 189, 149, 2, 218, 35, 160)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(95, 189, 69, 16, 47, 22, 203, 145)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(9, 192, 197, 98, 93, 34, 198, 167)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(114, 170, 107, 30, 69, 106, 9, 80)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 228, 26, 163, 2, 191, 47, 103)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 106, 161, 213, 213, 83, 190, 134)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 97, 137, 105, 223, 75, 255, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value),LEAN_SCALAR_PTR_LITERAL(53, 245, 46, 218, 50, 209, 251, 116)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value),LEAN_SCALAR_PTR_LITERAL(123, 250, 154, 0, 154, 13, 165, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 3, 181, 2, 27, 198, 42)}};
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; double v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_float_of_nat(v___x_27_);
return v___x_28_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(lean_object* v_cls_32_, lean_object* v_msg_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_ref_39_; lean_object* v___x_40_; lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_86_; 
v_ref_39_ = lean_ctor_get(v___y_36_, 2);
v___x_40_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msg_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_86_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_86_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_86_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v_traceState_46_; lean_object* v_env_47_; lean_object* v_nextMacroScope_48_; lean_object* v_ngen_49_; lean_object* v_auxDeclNGen_50_; lean_object* v_cache_51_; lean_object* v_recordedDeps_52_; lean_object* v_messages_53_; lean_object* v_infoState_54_; lean_object* v_snapshotTasks_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_85_; 
v___x_45_ = lean_st_ref_take(v___y_37_);
v_traceState_46_ = lean_ctor_get(v___x_45_, 4);
v_env_47_ = lean_ctor_get(v___x_45_, 0);
v_nextMacroScope_48_ = lean_ctor_get(v___x_45_, 1);
v_ngen_49_ = lean_ctor_get(v___x_45_, 2);
v_auxDeclNGen_50_ = lean_ctor_get(v___x_45_, 3);
v_cache_51_ = lean_ctor_get(v___x_45_, 5);
v_recordedDeps_52_ = lean_ctor_get(v___x_45_, 6);
v_messages_53_ = lean_ctor_get(v___x_45_, 7);
v_infoState_54_ = lean_ctor_get(v___x_45_, 8);
v_snapshotTasks_55_ = lean_ctor_get(v___x_45_, 9);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_85_ == 0)
{
v___x_57_ = v___x_45_;
v_isShared_58_ = v_isSharedCheck_85_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_snapshotTasks_55_);
lean_inc(v_infoState_54_);
lean_inc(v_messages_53_);
lean_inc(v_recordedDeps_52_);
lean_inc(v_cache_51_);
lean_inc(v_traceState_46_);
lean_inc(v_auxDeclNGen_50_);
lean_inc(v_ngen_49_);
lean_inc(v_nextMacroScope_48_);
lean_inc(v_env_47_);
lean_dec(v___x_45_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_85_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint64_t v_tid_59_; lean_object* v_traces_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_84_; 
v_tid_59_ = lean_ctor_get_uint64(v_traceState_46_, sizeof(void*)*1);
v_traces_60_ = lean_ctor_get(v_traceState_46_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_traceState_46_);
if (v_isSharedCheck_84_ == 0)
{
v___x_62_ = v_traceState_46_;
v_isShared_63_ = v_isSharedCheck_84_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_traces_60_);
lean_dec(v_traceState_46_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_84_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; double v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_64_ = lean_box(0);
v___x_65_ = lean_box(0);
v___x_66_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0);
v___x_67_ = 0;
v___x_68_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_69_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_69_, 0, v_cls_32_);
lean_ctor_set(v___x_69_, 1, v___x_65_);
lean_ctor_set(v___x_69_, 2, v___x_68_);
lean_ctor_set_float(v___x_69_, sizeof(void*)*3, v___x_66_);
lean_ctor_set_float(v___x_69_, sizeof(void*)*3 + 8, v___x_66_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*3 + 16, v___x_67_);
v___x_70_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2));
v___x_71_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v_a_41_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
lean_inc(v_ref_39_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v_ref_39_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = l_Lean_PersistentArray_push___redArg(v_traces_60_, v___x_72_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_73_);
v___x_75_ = v___x_62_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_73_);
lean_ctor_set_uint64(v_reuseFailAlloc_83_, sizeof(void*)*1, v_tid_59_);
v___x_75_ = v_reuseFailAlloc_83_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_77_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_75_);
v___x_77_ = v___x_57_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_env_47_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_nextMacroScope_48_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_ngen_49_);
lean_ctor_set(v_reuseFailAlloc_82_, 3, v_auxDeclNGen_50_);
lean_ctor_set(v_reuseFailAlloc_82_, 4, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_82_, 5, v_cache_51_);
lean_ctor_set(v_reuseFailAlloc_82_, 6, v_recordedDeps_52_);
lean_ctor_set(v_reuseFailAlloc_82_, 7, v_messages_53_);
lean_ctor_set(v_reuseFailAlloc_82_, 8, v_infoState_54_);
lean_ctor_set(v_reuseFailAlloc_82_, 9, v_snapshotTasks_55_);
v___x_77_ = v_reuseFailAlloc_82_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_st_ref_put(v___y_37_, v___x_77_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_64_);
v___x_80_ = v___x_43_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_64_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_32_ = stack[0].m_obj;
lean_object* v_msg_33_ = stack[1].m_obj;
lean_object* v___y_34_ = stack[2].m_obj;
lean_object* v___y_35_ = stack[3].m_obj;
lean_object* v___y_36_ = stack[4].m_obj;
lean_object* v___y_37_ = stack[5].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_32_, v_msg_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_88_, lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_88_, v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
if (lean_obj_tag(v_a_96_) == 0)
{
lean_object* v___x_98_; 
v___x_98_ = l_List_reverse___redArg(v_a_97_);
return v___x_98_;
}
else
{
lean_object* v_head_99_; lean_object* v_tail_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_109_; 
v_head_99_ = lean_ctor_get(v_a_96_, 0);
v_tail_100_ = lean_ctor_get(v_a_96_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_a_96_);
if (v_isSharedCheck_109_ == 0)
{
v___x_102_ = v_a_96_;
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_tail_100_);
lean_inc(v_head_99_);
lean_dec(v_a_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_MessageData_ofSyntax(v_head_99_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_a_97_);
lean_ctor_set(v___x_102_, 0, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_a_97_);
v___x_106_ = v_reuseFailAlloc_108_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
v_a_96_ = v_tail_100_;
v_a_97_ = v___x_106_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_box(1);
v___x_111_ = l_Lean_MessageData_ofFormat(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2));
v___x_116_ = l_Lean_MessageData_ofFormat(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
return v_x_117_;
}
else
{
lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_142_; 
v_head_119_ = lean_ctor_get(v_x_118_, 0);
v_tail_120_ = lean_ctor_get(v_x_118_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_118_);
if (v_isSharedCheck_142_ == 0)
{
v___x_122_ = v_x_118_;
v_isShared_123_ = v_isSharedCheck_142_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_tail_120_);
lean_inc(v_head_119_);
lean_dec(v_x_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_142_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_before_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_140_; 
v_before_124_ = lean_ctor_get(v_head_119_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_head_119_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_head_119_, 1);
lean_dec(v_unused_141_);
v___x_126_ = v_head_119_;
v_isShared_127_ = v_isSharedCheck_140_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_before_124_);
lean_dec(v_head_119_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_140_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 7);
lean_ctor_set(v___x_126_, 1, v___x_128_);
lean_ctor_set(v___x_126_, 0, v_x_117_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_x_117_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_139_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 7);
lean_ctor_set(v___x_122_, 1, v___x_131_);
lean_ctor_set(v___x_122_, 0, v___x_130_);
v___x_133_ = v___x_122_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_138_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = l_Lean_MessageData_ofSyntax(v_before_124_);
v___x_135_ = l_Lean_indentD(v___x_134_);
v___x_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_133_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v_x_117_ = v___x_136_;
v_x_118_ = v_tail_120_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(lean_object* v_opts_143_, lean_object* v_opt_144_){
_start:
{
lean_object* v_name_145_; lean_object* v_defValue_146_; lean_object* v_map_147_; lean_object* v___x_148_; 
v_name_145_ = lean_ctor_get(v_opt_144_, 0);
v_defValue_146_ = lean_ctor_get(v_opt_144_, 1);
v_map_147_ = lean_ctor_get(v_opts_143_, 0);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_147_, v_name_145_);
if (lean_obj_tag(v___x_148_) == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_unbox(v_defValue_146_);
return v___x_149_;
}
else
{
lean_object* v_val_150_; 
v_val_150_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v___x_148_, 1);
if (lean_obj_tag(v_val_150_) == 1)
{
uint8_t v_v_151_; 
v_v_151_ = lean_ctor_get_uint8(v_val_150_, 0);
lean_dec_ref_known(v_val_150_, 0);
return v_v_151_;
}
else
{
uint8_t v___x_152_; 
lean_dec(v_val_150_);
v___x_152_ = lean_unbox(v_defValue_146_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_143_ = stack[0].m_obj;
lean_object* v_opt_144_ = stack[1].m_obj;
uint8_t v_res_153_;
v_res_153_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_143_, v_opt_144_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(lean_object* v_opts_154_, lean_object* v_opt_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_154_, v_opt_155_);
lean_dec_ref(v_opt_155_);
lean_dec_ref(v_opts_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1));
v___x_162_ = l_Lean_MessageData_ofFormat(v___x_161_);
return v___x_162_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(lean_object* v_msgData_163_, lean_object* v_macroStack_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_167_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_165_);
v___x_168_ = l_Lean_Elab_pp_macroStack;
v___x_169_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v___x_167_, v___x_168_);
lean_dec_ref(v___x_167_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v_macroStack_164_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v_msgData_163_);
return v___x_170_;
}
else
{
if (lean_obj_tag(v_macroStack_164_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_msgData_163_);
return v___x_171_;
}
else
{
lean_object* v_head_172_; lean_object* v_after_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_188_; 
v_head_172_ = lean_ctor_get(v_macroStack_164_, 0);
lean_inc(v_head_172_);
v_after_173_ = lean_ctor_get(v_head_172_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_head_172_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_head_172_, 0);
lean_dec(v_unused_189_);
v___x_175_ = v_head_172_;
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_after_173_);
lean_dec(v_head_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_176_ == 0)
{
lean_ctor_set_tag(v___x_175_, 7);
lean_ctor_set(v___x_175_, 1, v___x_177_);
lean_ctor_set(v___x_175_, 0, v_msgData_163_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_msgData_163_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_187_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_msgData_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_180_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2);
v___x_181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = l_Lean_MessageData_ofSyntax(v_after_173_);
v___x_183_ = l_Lean_indentD(v___x_182_);
v_msgData_184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_184_, 0, v___x_181_);
lean_ctor_set(v_msgData_184_, 1, v___x_183_);
v___x_185_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(v_msgData_184_, v_macroStack_164_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_163_ = stack[0].m_obj;
lean_object* v_macroStack_164_ = stack[1].m_obj;
lean_object* v___y_165_ = stack[2].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_163_, v_macroStack_164_, v___y_165_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_191_, lean_object* v_macroStack_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_191_, v_macroStack_192_, v___y_193_);
lean_dec_ref(v___y_193_);
return v_res_195_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(lean_object* v_msg_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_ref_204_; lean_object* v_macroStack_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_ref_204_ = lean_ctor_get(v___y_201_, 2);
v_macroStack_205_ = lean_ctor_get(v___y_197_, 1);
v___x_206_ = l_Lean_Elab_getBetterRef(v_ref_204_, v_macroStack_205_);
v___x_207_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msg_196_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
lean_inc(v_macroStack_205_);
v___x_209_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_a_208_, v_macroStack_205_, v___y_201_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_218_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_206_);
lean_ctor_set(v___x_214_, 1, v_a_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 1);
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_196_ = stack[0].m_obj;
lean_object* v___y_197_ = stack[1].m_obj;
lean_object* v___y_198_ = stack[2].m_obj;
lean_object* v___y_199_ = stack[3].m_obj;
lean_object* v___y_200_ = stack[4].m_obj;
lean_object* v___y_201_ = stack[5].m_obj;
lean_object* v___y_202_ = stack[6].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___boxed(lean_object* v_msg_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0));
v___x_231_ = l_Lean_stringToMessageData(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(lean_object* v_constName_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; lean_object* v_env_244_; lean_object* v___x_245_; 
v___x_243_ = lean_st_ref_get(v___y_241_);
v_env_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref(v_env_244_);
lean_dec(v___x_243_);
lean_inc(v_constName_235_);
v___x_245_ = l_Lean_isInductiveCore_x3f(v_env_244_, v_constName_235_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_246_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1);
v___x_247_ = 0;
v___x_248_ = l_Lean_MessageData_ofConstName(v_constName_235_, v___x_247_);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_251_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
return v___x_252_;
}
else
{
lean_object* v_val_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_constName_235_);
v_val_253_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_245_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_val_253_);
lean_dec(v___x_245_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 0);
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_val_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_235_ = stack[0].m_obj;
lean_object* v___y_236_ = stack[1].m_obj;
lean_object* v___y_237_ = stack[2].m_obj;
lean_object* v___y_238_ = stack[3].m_obj;
lean_object* v___y_239_ = stack[4].m_obj;
lean_object* v___y_240_ = stack[5].m_obj;
lean_object* v___y_241_ = stack[6].m_obj;
lean_object* v_res_261_;
v_res_261_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_constName_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___boxed(lean_object* v_constName_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_constName_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6));
v___x_290_ = l_Lean_mkCIdent(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Array_mkArray0___redArg();
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36));
v___x_357_ = l_String_toRawSubstring_x27(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_410_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61));
v___x_411_ = l_Lean_Name_append(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63));
v___x_414_ = l_Lean_stringToMessageData(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(lean_object* v_declName_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_declName_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v_all_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v_all_601_ = lean_ctor_get(v_a_430_, 3);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = l_List_lengthTR___redArg(v_all_601_);
v___x_604_ = lean_nat_dec_lt(v___x_602_, v___x_603_);
lean_dec(v___x_603_);
if (v___x_604_ == 0)
{
v___y_584_ = v_a_422_;
v___y_585_ = v_a_423_;
v___y_586_ = v_a_424_;
v___y_587_ = v_a_425_;
v___y_588_ = v_a_426_;
v___y_589_ = v_a_427_;
goto v___jp_583_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v_a_430_);
v___x_605_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68);
v___x_606_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_605_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
v___jp_431_:
{
lean_object* v___x_438_; 
lean_inc(v_a_430_);
v___x_438_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_430_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_n(v_a_439_, 2);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_439_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1));
lean_inc(v_a_439_);
lean_inc(v_a_430_);
v___x_443_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_442_, v_a_430_, v_a_439_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = l_Array_append___redArg(v_a_441_, v_a_444_);
lean_dec(v_a_444_);
v___x_446_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6));
lean_inc(v_a_439_);
lean_inc(v_a_430_);
v___x_447_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_446_, v_a_430_, v_a_439_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Array_append___redArg(v___x_445_, v_a_448_);
lean_dec(v_a_448_);
v___x_450_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_430_, v_a_439_, v___y_436_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_toCold_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_558_; 
v_toCold_451_ = lean_ctor_get(v___y_436_, 0);
v_a_452_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_558_ == 0)
{
v___x_454_ = v___x_450_;
v_isShared_455_ = v_isSharedCheck_558_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_558_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_ref_456_; lean_object* v_options_457_; lean_object* v_quotContext_458_; lean_object* v_currMacroScope_459_; lean_object* v_inheritedTraceOptions_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v_hasTrace_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_ref_456_ = lean_ctor_get(v___y_436_, 2);
v_options_457_ = lean_ctor_get(v_toCold_451_, 2);
v_quotContext_458_ = lean_ctor_get(v_toCold_451_, 8);
v_currMacroScope_459_ = lean_ctor_get(v_toCold_451_, 9);
v_inheritedTraceOptions_460_ = lean_ctor_get(v_toCold_451_, 11);
v___x_461_ = 0;
v___x_462_ = l_Lean_SourceInfo_fromRef(v_ref_456_, v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8));
lean_inc_n(v___x_462_, 28);
v___x_464_ = l_Lean_Syntax_node1(v___x_462_, v___x_463_, v_a_452_);
v___x_465_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10));
v___x_466_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11);
v___x_467_ = l_Lean_Syntax_node2(v___x_462_, v___x_465_, v___x_466_, v___x_464_);
v___x_468_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14));
v___x_469_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16));
v___x_470_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_462_);
lean_ctor_set(v___x_471_, 1, v___x_463_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
lean_inc_ref_n(v___x_471_, 14);
v___x_472_ = l_Lean_Syntax_node7(v___x_462_, v___x_469_, v___x_471_, v___x_471_, v___x_471_, v___x_471_, v___x_471_, v___x_471_, v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18));
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19));
v___x_475_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21));
v___x_476_ = l_Lean_Syntax_node1(v___x_462_, v___x_475_, v___x_471_);
v___x_477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_462_);
lean_ctor_set(v___x_477_, 1, v___x_473_);
v___x_478_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23));
v___x_479_ = l_Array_append___redArg(v___x_470_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v___x_462_);
lean_ctor_set(v___x_480_, 1, v___x_463_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25));
v___x_482_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26));
v___x_483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_462_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_Syntax_node2(v___x_462_, v___x_481_, v___x_483_, v___x_467_);
v___x_485_ = l_Lean_Syntax_node2(v___x_462_, v___x_478_, v___x_480_, v___x_484_);
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28));
v___x_487_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29));
v___x_488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_462_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31));
v___x_490_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33));
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35));
v___x_492_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37);
v___x_493_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38));
lean_inc(v_currMacroScope_459_);
lean_inc(v_quotContext_458_);
v___x_494_ = l_Lean_addMacroScope(v_quotContext_458_, v___x_493_, v_currMacroScope_459_);
v___x_495_ = lean_box(0);
v___x_496_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40));
v___x_497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_497_, 0, v___x_462_);
lean_ctor_set(v___x_497_, 1, v___x_492_);
lean_ctor_set(v___x_497_, 2, v___x_494_);
lean_ctor_set(v___x_497_, 3, v___x_496_);
v___x_498_ = l_Lean_Syntax_node2(v___x_462_, v___x_491_, v___x_497_, v___x_471_);
v___x_499_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42));
v___x_500_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_462_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45));
v___x_503_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46));
v___x_504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_462_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49));
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51));
v___x_507_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54));
v___x_508_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55));
v___x_509_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_462_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_Syntax_node1(v___x_462_, v___x_507_, v___x_509_);
v___x_511_ = l_Lean_Syntax_node1(v___x_462_, v___x_463_, v___x_510_);
v___x_512_ = l_Lean_Syntax_node1(v___x_462_, v___x_506_, v___x_511_);
v___x_513_ = l_Lean_Syntax_node1(v___x_462_, v___x_505_, v___x_512_);
v___x_514_ = l_Lean_Syntax_node2(v___x_462_, v___x_502_, v___x_504_, v___x_513_);
v___x_515_ = l_Lean_Syntax_node3(v___x_462_, v___x_499_, v___x_501_, v___x_471_, v___x_514_);
v___x_516_ = l_Lean_Syntax_node3(v___x_462_, v___x_463_, v___x_471_, v___x_471_, v___x_515_);
v___x_517_ = l_Lean_Syntax_node2(v___x_462_, v___x_490_, v___x_498_, v___x_516_);
v___x_518_ = l_Lean_Syntax_node1(v___x_462_, v___x_463_, v___x_517_);
v___x_519_ = l_Lean_Syntax_node1(v___x_462_, v___x_489_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node3(v___x_462_, v___x_486_, v___x_488_, v___x_519_, v___x_471_);
v___x_521_ = l_Lean_Syntax_node6(v___x_462_, v___x_474_, v___x_476_, v___x_477_, v___x_471_, v___x_471_, v___x_485_, v___x_520_);
v_hasTrace_522_ = lean_ctor_get_uint8(v_options_457_, sizeof(void*)*1);
v___x_523_ = l_Lean_Syntax_node2(v___x_462_, v___x_468_, v___x_472_, v___x_521_);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_mk_empty_array_with_capacity(v___x_524_);
v___x_526_ = lean_array_push(v___x_525_, v___x_523_);
if (v_hasTrace_522_ == 0)
{
lean_object* v___x_528_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_526_);
v___x_528_ = v___x_454_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_531_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62);
v___x_532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_460_, v_options_457_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_534_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_526_);
v___x_534_ = v___x_454_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_526_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_del_object(v___x_454_);
v___x_536_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64);
lean_inc_ref(v___x_526_);
v___x_537_ = lean_array_to_list(v___x_526_);
v___x_538_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(v___x_537_, v___x_495_);
v___x_539_ = l_Lean_MessageData_ofList(v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_536_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v___x_530_, v___x_540_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_549_);
v___x_543_ = v___x_541_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_541_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_526_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_526_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v___x_526_);
v_a_550_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_541_);
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
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v___x_449_);
v_a_559_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_450_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_450_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_dec_ref(v___x_445_);
lean_dec(v_a_439_);
lean_dec(v_a_430_);
return v___x_447_;
}
}
else
{
lean_dec(v_a_441_);
lean_dec(v_a_439_);
lean_dec(v_a_430_);
return v___x_443_;
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_a_439_);
lean_dec(v_a_430_);
v_a_567_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_440_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_440_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_a_430_);
v_a_575_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_438_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_438_);
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
v___jp_583_:
{
uint8_t v___x_590_; 
v___x_590_ = l_Lean_InductiveVal_isNested(v_a_430_);
if (v___x_590_ == 0)
{
v___y_432_ = v___y_584_;
v___y_433_ = v___y_585_;
v___y_434_ = v___y_586_;
v___y_435_ = v___y_587_;
v___y_436_ = v___y_588_;
v___y_437_ = v___y_589_;
goto v___jp_431_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_a_430_);
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66);
v___x_592_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_591_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_429_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_429_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_421_ = stack[0].m_obj;
lean_object* v_a_422_ = stack[1].m_obj;
lean_object* v_a_423_ = stack[2].m_obj;
lean_object* v_a_424_ = stack[3].m_obj;
lean_object* v_a_425_ = stack[4].m_obj;
lean_object* v_a_426_ = stack[5].m_obj;
lean_object* v_a_427_ = stack[6].m_obj;
lean_object* v_res_623_;
v_res_623_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(v_declName_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed(lean_object* v_declName_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(v_declName_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_632_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(lean_object* v_cls_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_633_, v_msg_634_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_633_ = stack[0].m_obj;
lean_object* v_msg_634_ = stack[1].m_obj;
lean_object* v___y_635_ = stack[2].m_obj;
lean_object* v___y_636_ = stack[3].m_obj;
lean_object* v___y_637_ = stack[4].m_obj;
lean_object* v___y_638_ = stack[5].m_obj;
lean_object* v___y_639_ = stack[6].m_obj;
lean_object* v___y_640_ = stack[7].m_obj;
lean_object* v_res_643_;
v_res_643_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(v_cls_633_, v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___boxed(lean_object* v_cls_644_, lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(v_cls_644_, v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_653_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_663_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_655_ = stack[1].m_obj;
lean_object* v___y_656_ = stack[2].m_obj;
lean_object* v___y_657_ = stack[3].m_obj;
lean_object* v___y_658_ = stack[4].m_obj;
lean_object* v___y_659_ = stack[5].m_obj;
lean_object* v___y_660_ = stack[6].m_obj;
lean_object* v___y_661_ = stack[7].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(lean_box(0), v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___boxed(lean_object* v_00_u03b1_665_, lean_object* v_msg_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(v_00_u03b1_665_, v_msg_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
return v_res_674_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(lean_object* v_msgData_675_, lean_object* v_macroStack_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_675_, v_macroStack_676_, v___y_681_);
return v___x_684_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_675_ = stack[0].m_obj;
lean_object* v_macroStack_676_ = stack[1].m_obj;
lean_object* v___y_677_ = stack[2].m_obj;
lean_object* v___y_678_ = stack[3].m_obj;
lean_object* v___y_679_ = stack[4].m_obj;
lean_object* v___y_680_ = stack[5].m_obj;
lean_object* v___y_681_ = stack[6].m_obj;
lean_object* v___y_682_ = stack[7].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(v_msgData_675_, v_macroStack_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___boxed(lean_object* v_msgData_686_, lean_object* v_macroStack_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(v_msgData_686_, v_macroStack_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_695_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(lean_object* v_as_696_, size_t v_i_697_, size_t v_stop_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_eq(v_i_697_, v_stop_698_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_array_uget_borrowed(v_as_696_, v_i_697_);
lean_inc(v___x_704_);
v___x_705_ = l_Lean_Elab_Command_elabCommand(v___x_704_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; size_t v___x_707_; size_t v___x_708_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_697_, v___x_707_);
v_i_697_ = v___x_708_;
v_b_699_ = v_a_706_;
goto _start;
}
else
{
return v___x_705_;
}
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_b_699_);
return v___x_710_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_696_ = stack[0].m_obj;
size_t v_i_697_ = stack[1].m_num;
size_t v_stop_698_ = stack[2].m_num;
lean_object* v_b_699_ = stack[3].m_obj;
lean_object* v___y_700_ = stack[4].m_obj;
lean_object* v___y_701_ = stack[5].m_obj;
lean_object* v_res_711_;
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_as_696_, v_i_697_, v_stop_698_, v_b_699_, v___y_700_, v___y_701_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0___boxed(lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_stop_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
size_t v_i_boxed_719_; size_t v_stop_boxed_720_; lean_object* v_res_721_; 
v_i_boxed_719_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_stop_boxed_720_ = lean_unbox_usize(v_stop_714_);
lean_dec(v_stop_714_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_as_712_, v_i_boxed_719_, v_stop_boxed_720_, v_b_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_as_712_);
return v_res_721_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(lean_object* v___x_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_748_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_748_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_748_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_748_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_array_get_size(v_a_727_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_nat_dec_lt(v___x_731_, v___x_732_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v_a_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_736_ = v___x_729_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
uint8_t v___x_738_; 
v___x_738_ = lean_nat_dec_le(v___x_732_, v___x_732_);
if (v___x_738_ == 0)
{
if (v___x_734_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v_a_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_740_ = v___x_729_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_733_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
lean_del_object(v___x_729_);
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_732_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_727_, v___x_742_, v___x_743_, v___x_733_, v___y_723_, v___y_724_);
lean_dec(v_a_727_);
return v___x_744_;
}
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_729_);
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_732_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_727_, v___x_745_, v___x_746_, v___x_733_, v___y_723_, v___y_724_);
lean_dec(v_a_727_);
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
v_a_749_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_726_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_726_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_722_ = stack[0].m_obj;
lean_object* v___y_723_ = stack[1].m_obj;
lean_object* v___y_724_ = stack[2].m_obj;
lean_object* v_res_757_;
v_res_757_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(v___x_722_, v___y_723_, v___y_724_);
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed(lean_object* v___x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(v___x_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_762_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(lean_object* v_declName_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___x_769_; 
lean_inc(v_declName_763_);
v___x_767_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_767_, 0, v_declName_763_);
v___f_768_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(v___f_768_, 0, v___x_767_);
v___x_769_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_763_, v___f_768_, v_a_764_, v_a_765_);
return v___x_769_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_763_ = stack[0].m_obj;
lean_object* v_a_764_ = stack[1].m_obj;
lean_object* v_a_765_ = stack[2].m_obj;
lean_object* v_res_770_;
v_res_770_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_declName_763_, v_a_764_, v_a_765_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___boxed(lean_object* v_declName_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_declName_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_775_;
}
}
lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; lean_object* v_env_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_779_ = lean_st_ref_get(v___y_777_);
v_env_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc_ref(v_env_780_);
lean_dec(v___x_779_);
v___x_781_ = l_Lean_isInductiveCore(v_env_780_, v_declName_776_);
v___x_782_ = lean_box(v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_776_ = stack[0].m_obj;
lean_object* v___y_777_ = stack[1].m_obj;
lean_object* v_res_784_;
v_res_784_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_776_, v___y_777_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_785_, v___y_786_);
lean_dec(v___y_786_);
return v_res_788_;
}
}
lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(lean_object* v_declName_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_789_, v___y_791_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_789_ = stack[0].m_obj;
lean_object* v___y_790_ = stack[1].m_obj;
lean_object* v___y_791_ = stack[2].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(v_declName_789_, v___y_790_, v___y_791_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(v_declName_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_799_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(uint8_t v_____do__lift_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
if (v_____do__lift_800_ == 0)
{
uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = 1;
v___x_805_ = lean_box(v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
else
{
uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = 0;
v___x_808_ = lean_box(v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_800_ = stack[0].m_num;
lean_object* v___y_801_ = stack[1].m_obj;
lean_object* v___y_802_ = stack[2].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v_____do__lift_800_, v___y_801_, v___y_802_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v_____do__lift_1669__boxed_815_; lean_object* v_res_816_; 
v_____do__lift_1669__boxed_815_ = lean_unbox(v_____do__lift_811_);
v_res_816_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v_____do__lift_1669__boxed_815_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_816_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(lean_object* v_as_817_, size_t v_i_818_, size_t v_stop_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_eq(v_i_818_, v_stop_819_);
if (v___x_827_ == 0)
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = 1;
v___x_829_ = lean_array_uget_borrowed(v_as_817_, v_i_818_);
lean_inc(v___x_829_);
v___x_830_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v___x_829_, v___y_821_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_840_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_840_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
uint8_t v___x_835_; 
v___x_835_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_box(v___x_828_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_del_object(v___x_833_);
goto v___jp_823_;
}
}
}
else
{
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_850_; 
v_a_841_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_850_ == 0)
{
v___x_843_ = v___x_830_;
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_830_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; 
v___x_845_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_845_ == 0)
{
lean_del_object(v___x_843_);
goto v___jp_823_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_box(v___x_828_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
return v___x_830_;
}
}
}
else
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = 0;
v___x_852_ = lean_box(v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
v___jp_823_:
{
size_t v___x_824_; size_t v___x_825_; 
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_i_818_, v___x_824_);
v_i_818_ = v___x_825_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_817_ = stack[0].m_obj;
size_t v_i_818_ = stack[1].m_num;
size_t v_stop_819_ = stack[2].m_num;
lean_object* v___y_820_ = stack[3].m_obj;
lean_object* v___y_821_ = stack[4].m_obj;
lean_object* v_res_854_;
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_as_817_, v_i_818_, v_stop_819_, v___y_820_, v___y_821_);
stack->m_obj
 = v_res_854_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(lean_object* v_as_864_, size_t v_sz_865_, size_t v_i_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = lean_usize_dec_lt(v_i_866_, v_sz_865_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_b_867_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v_a_874_; lean_object* v___x_875_; 
v___x_873_ = lean_box(0);
v_a_874_ = lean_array_uget_borrowed(v_as_864_, v_i_866_);
lean_inc(v_a_874_);
v___x_875_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_a_874_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_875_) == 0)
{
size_t v___x_876_; size_t v___x_877_; 
lean_dec_ref_known(v___x_875_, 1);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_866_, v___x_876_);
v_i_866_ = v___x_877_;
v_b_867_ = v___x_873_;
goto _start;
}
else
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_864_ = stack[0].m_obj;
size_t v_sz_865_ = stack[1].m_num;
size_t v_i_866_ = stack[2].m_num;
lean_object* v_b_867_ = stack[3].m_obj;
lean_object* v___y_868_ = stack[4].m_obj;
lean_object* v___y_869_ = stack[5].m_obj;
lean_object* v_res_879_;
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_as_864_, v_sz_865_, v_i_866_, v_b_867_, v___y_868_, v___y_869_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0___boxed(lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
size_t v_sz_boxed_887_; size_t v_i_boxed_888_; lean_object* v_res_889_; 
v_sz_boxed_887_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_888_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_as_880_, v_sz_boxed_887_, v_i_boxed_888_, v_b_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_as_880_);
return v_res_889_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(lean_object* v_declNames_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___y_918_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_array_get_size(v_declNames_890_);
v___x_923_ = lean_nat_dec_lt(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_923_, v_a_891_, v_a_892_);
v___y_918_ = v___x_924_;
goto v___jp_917_;
}
else
{
if (v___x_923_ == 0)
{
goto v___jp_894_;
}
else
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_922_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_declNames_890_, v___x_925_, v___x_926_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; uint8_t v___x_929_; lean_object* v___x_930_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = lean_unbox(v_a_928_);
lean_dec(v_a_928_);
v___x_930_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_929_, v_a_891_, v_a_892_);
v___y_918_ = v___x_930_;
goto v___jp_917_;
}
else
{
v___y_918_ = v___x_927_;
goto v___jp_917_;
}
}
}
v___jp_894_:
{
uint8_t v___x_895_; lean_object* v___x_896_; size_t v_sz_897_; size_t v___x_898_; lean_object* v___x_899_; 
v___x_895_ = 1;
v___x_896_ = lean_box(0);
v_sz_897_ = lean_array_size(v_declNames_890_);
v___x_898_ = ((size_t)0ULL);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_declNames_890_, v_sz_897_, v___x_898_, v___x_896_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_908_);
v___x_901_ = v___x_899_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_dec(v___x_899_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_box(v___x_895_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_899_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
v___jp_917_:
{
if (lean_obj_tag(v___y_918_) == 0)
{
lean_object* v_a_919_; uint8_t v___x_920_; 
v_a_919_ = lean_ctor_get(v___y_918_, 0);
v___x_920_ = lean_unbox(v_a_919_);
if (v___x_920_ == 0)
{
return v___y_918_;
}
else
{
lean_dec_ref_known(v___y_918_, 1);
goto v___jp_894_;
}
}
else
{
return v___y_918_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_890_ = stack[0].m_obj;
lean_object* v_a_891_ = stack[1].m_obj;
lean_object* v_a_892_ = stack[2].m_obj;
lean_object* v_res_931_;
v_res_931_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(v_declNames_890_, v_a_891_, v_a_892_);
stack->m_obj
 = v_res_931_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed(lean_object* v_declNames_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(v_declNames_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec_ref(v_declNames_932_);
return v_res_936_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6));
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_));
v___x_1006_ = l_Lean_Elab_registerDerivingHandler(v___x_1004_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec_ref_known(v___x_1006_, 1);
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_1008_ = 0;
v___x_1009_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_));
v___x_1010_ = l_Lean_registerTraceClass(v___x_1007_, v___x_1008_, v___x_1009_);
return v___x_1010_;
}
else
{
return v___x_1006_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1011_;
v_res_1011_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2____boxed(lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
return v_res_1013_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_ReflBEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
