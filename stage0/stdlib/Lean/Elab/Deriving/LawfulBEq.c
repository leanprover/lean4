// Lean compiler output
// Module: Lean.Elab.Deriving.LawfulBEq
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
uint8_t l_Lean_InductiveVal_isNested(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LawfulBEq"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LawfulBEq.mk"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 227, 222, 64, 229, 226, 161)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(239, 216, 42, 178, 87, 188, 183, 65)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TSyntax"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Compat"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value),LEAN_SCALAR_PTR_LITERAL(233, 134, 124, 217, 96, 118, 79, 86)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "tacticDeriving_LawfulEq_tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72_value),LEAN_SCALAR_PTR_LITERAL(223, 236, 164, 161, 104, 237, 167, 171)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "deriving_LawfulEq_tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lawfulBEq"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79_value),LEAN_SCALAR_PTR_LITERAL(105, 144, 65, 135, 21, 116, 188, 189)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Deriving `LawfulBEq` for nested inductives is not supported"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Deriving `LawfulBEq` for mutual inductives is not supported"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 141, 19, 219, 57, 63, 124, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(54, 195, 48, 34, 119, 0, 161, 186)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(95, 238, 135, 22, 62, 57, 216, 235)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(193, 79, 119, 168, 243, 41, 160, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(87, 78, 239, 73, 65, 82, 155, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(234, 37, 17, 192, 254, 35, 185, 251)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 230, 17, 18, 16, 137, 34, 13)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 122, 229, 163, 241, 81, 47, 255)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 49, 66, 28, 93, 238, 35, 16)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(13, 99, 135, 253, 30, 131, 204, 96)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(195, 203, 159, 105, 27, 114, 67, 184)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 88, 198, 182, 153, 159, 57)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_9_ = l_Lean_MessageData_ofSyntax(v_head_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_a_2_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_11_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(lean_object* v_opts_15_, lean_object* v_opt_16_){
_start:
{
lean_object* v_name_17_; lean_object* v_defValue_18_; lean_object* v_map_19_; lean_object* v___x_20_; 
v_name_17_ = lean_ctor_get(v_opt_16_, 0);
v_defValue_18_ = lean_ctor_get(v_opt_16_, 1);
v_map_19_ = lean_ctor_get(v_opts_15_, 0);
v___x_20_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_19_, v_name_17_);
if (lean_obj_tag(v___x_20_) == 0)
{
uint8_t v___x_21_; 
v___x_21_ = lean_unbox(v_defValue_18_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; 
v_val_22_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v___x_20_, 1);
if (lean_obj_tag(v_val_22_) == 1)
{
uint8_t v_v_23_; 
v_v_23_ = lean_ctor_get_uint8(v_val_22_, 0);
lean_dec_ref_known(v_val_22_, 0);
return v_v_23_;
}
else
{
uint8_t v___x_24_; 
lean_dec(v_val_22_);
v___x_24_ = lean_unbox(v_defValue_18_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(lean_object* v_opts_25_, lean_object* v_opt_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_25_, v_opt_26_);
lean_dec_ref(v_opt_26_);
lean_dec_ref(v_opts_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_box(1);
v___x_30_ = l_Lean_MessageData_ofFormat(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2));
v___x_35_ = l_Lean_MessageData_ofFormat(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(lean_object* v_x_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
return v_x_36_;
}
else
{
lean_object* v_head_38_; lean_object* v_tail_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_61_; 
v_head_38_ = lean_ctor_get(v_x_37_, 0);
v_tail_39_ = lean_ctor_get(v_x_37_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_61_ == 0)
{
v___x_41_ = v_x_37_;
v_isShared_42_ = v_isSharedCheck_61_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_tail_39_);
lean_inc(v_head_38_);
lean_dec(v_x_37_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_61_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_before_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_59_; 
v_before_43_ = lean_ctor_get(v_head_38_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v_head_38_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v_head_38_, 1);
lean_dec(v_unused_60_);
v___x_45_ = v_head_38_;
v_isShared_46_ = v_isSharedCheck_59_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_before_43_);
lean_dec(v_head_38_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_59_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 7);
lean_ctor_set(v___x_45_, 1, v___x_47_);
lean_ctor_set(v___x_45_, 0, v_x_36_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_x_36_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_58_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3);
if (v_isShared_42_ == 0)
{
lean_ctor_set_tag(v___x_41_, 7);
lean_ctor_set(v___x_41_, 1, v___x_50_);
lean_ctor_set(v___x_41_, 0, v___x_49_);
v___x_52_ = v___x_41_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_57_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = l_Lean_MessageData_ofSyntax(v_before_43_);
v___x_54_ = l_Lean_indentD(v___x_53_);
v___x_55_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_52_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v_x_36_ = v___x_55_;
v_x_37_ = v_tail_39_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1));
v___x_66_ = l_Lean_MessageData_ofFormat(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(lean_object* v_msgData_67_, lean_object* v_macroStack_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_69_);
v___x_72_ = l_Lean_Elab_pp_macroStack;
v___x_73_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v___x_71_, v___x_72_);
lean_dec_ref(v___x_71_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
lean_dec(v_macroStack_68_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v_msgData_67_);
return v___x_74_;
}
else
{
if (lean_obj_tag(v_macroStack_68_) == 0)
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_msgData_67_);
return v___x_75_;
}
else
{
lean_object* v_head_76_; lean_object* v_after_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_92_; 
v_head_76_ = lean_ctor_get(v_macroStack_68_, 0);
lean_inc(v_head_76_);
v_after_77_ = lean_ctor_get(v_head_76_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_head_76_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_head_76_, 0);
lean_dec(v_unused_93_);
v___x_79_ = v_head_76_;
v_isShared_80_ = v_isSharedCheck_92_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_after_77_);
lean_dec(v_head_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_92_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 7);
lean_ctor_set(v___x_79_, 1, v___x_81_);
lean_ctor_set(v___x_79_, 0, v_msgData_67_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_msgData_67_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_81_);
v___x_83_ = v_reuseFailAlloc_91_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_msgData_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_84_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = l_Lean_MessageData_ofSyntax(v_after_77_);
v___x_87_ = l_Lean_indentD(v___x_86_);
v_msgData_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_88_, 0, v___x_85_);
lean_ctor_set(v_msgData_88_, 1, v___x_87_);
v___x_89_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(v_msgData_88_, v_macroStack_68_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_94_, lean_object* v_macroStack_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_94_, v_macroStack_95_, v___y_96_);
lean_dec_ref(v___y_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_env_106_; uint8_t v___x_107_; lean_object* v_env_108_; lean_object* v___x_109_; lean_object* v_toCold_110_; lean_object* v_mctx_111_; lean_object* v_lctx_112_; lean_object* v_options_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = 0;
v_env_108_ = l_Lean_Environment_setRecordingDeps(v_env_106_, v___x_107_);
v___x_109_ = lean_st_ref_get(v___y_101_);
v_toCold_110_ = lean_ctor_get(v___y_102_, 0);
v_mctx_111_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_mctx_111_);
lean_dec(v___x_109_);
v_lctx_112_ = lean_ctor_get(v___y_100_, 2);
v_options_113_ = lean_ctor_get(v_toCold_110_, 2);
lean_inc_ref(v_options_113_);
lean_inc_ref(v_lctx_112_);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v_env_108_);
lean_ctor_set(v___x_114_, 1, v_mctx_111_);
lean_ctor_set(v___x_114_, 2, v_lctx_112_);
lean_ctor_set(v___x_114_, 3, v_options_113_);
v___x_115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_msgData_99_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2___boxed(lean_object* v_msgData_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msgData_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_ref_132_; lean_object* v_macroStack_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_ref_132_ = lean_ctor_get(v___y_129_, 2);
v_macroStack_133_ = lean_ctor_get(v___y_125_, 1);
v___x_134_ = l_Lean_Elab_getBetterRef(v_ref_132_, v_macroStack_133_);
v___x_135_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_124_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref(v___x_135_);
lean_inc(v_macroStack_133_);
v___x_137_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_a_136_, v_macroStack_133_, v___y_129_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_134_);
lean_ctor_set(v___x_142_, 1, v_a_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 1);
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg___boxed(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_155_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0));
v___x_158_ = l_Lean_stringToMessageData(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2));
v___x_161_ = l_Lean_stringToMessageData(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(lean_object* v_constName_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; lean_object* v_env_171_; lean_object* v___x_172_; 
v___x_170_ = lean_st_ref_get(v___y_168_);
v_env_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc_ref(v_env_171_);
lean_dec(v___x_170_);
lean_inc(v_constName_162_);
v___x_172_ = l_Lean_isInductiveCore_x3f(v_env_171_, v_constName_162_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_173_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1);
v___x_174_ = 0;
v___x_175_ = l_Lean_MessageData_ofConstName(v_constName_162_, v___x_174_);
v___x_176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_173_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3);
v___x_178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_178_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_constName_162_);
v_val_180_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_172_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v___x_172_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set_tag(v___x_182_, 0);
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_val_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___boxed(lean_object* v_constName_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_constName_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_196_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_197_; double v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_float_of_nat(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(lean_object* v_cls_202_, lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_ref_209_; lean_object* v___x_210_; lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_256_; 
v_ref_209_ = lean_ctor_get(v___y_206_, 2);
v___x_210_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_256_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_256_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_256_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v_traceState_216_; lean_object* v_env_217_; lean_object* v_nextMacroScope_218_; lean_object* v_ngen_219_; lean_object* v_auxDeclNGen_220_; lean_object* v_cache_221_; lean_object* v_recordedDeps_222_; lean_object* v_messages_223_; lean_object* v_infoState_224_; lean_object* v_snapshotTasks_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_255_; 
v___x_215_ = lean_st_ref_take(v___y_207_);
v_traceState_216_ = lean_ctor_get(v___x_215_, 4);
v_env_217_ = lean_ctor_get(v___x_215_, 0);
v_nextMacroScope_218_ = lean_ctor_get(v___x_215_, 1);
v_ngen_219_ = lean_ctor_get(v___x_215_, 2);
v_auxDeclNGen_220_ = lean_ctor_get(v___x_215_, 3);
v_cache_221_ = lean_ctor_get(v___x_215_, 5);
v_recordedDeps_222_ = lean_ctor_get(v___x_215_, 6);
v_messages_223_ = lean_ctor_get(v___x_215_, 7);
v_infoState_224_ = lean_ctor_get(v___x_215_, 8);
v_snapshotTasks_225_ = lean_ctor_get(v___x_215_, 9);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_255_ == 0)
{
v___x_227_ = v___x_215_;
v_isShared_228_ = v_isSharedCheck_255_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_snapshotTasks_225_);
lean_inc(v_infoState_224_);
lean_inc(v_messages_223_);
lean_inc(v_recordedDeps_222_);
lean_inc(v_cache_221_);
lean_inc(v_traceState_216_);
lean_inc(v_auxDeclNGen_220_);
lean_inc(v_ngen_219_);
lean_inc(v_nextMacroScope_218_);
lean_inc(v_env_217_);
lean_dec(v___x_215_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_255_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
uint64_t v_tid_229_; lean_object* v_traces_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_254_; 
v_tid_229_ = lean_ctor_get_uint64(v_traceState_216_, sizeof(void*)*1);
v_traces_230_ = lean_ctor_get(v_traceState_216_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_traceState_216_);
if (v_isSharedCheck_254_ == 0)
{
v___x_232_ = v_traceState_216_;
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_traces_230_);
lean_dec(v_traceState_216_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; double v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_234_ = lean_box(0);
v___x_235_ = lean_box(0);
v___x_236_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0);
v___x_237_ = 0;
v___x_238_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_239_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_239_, 0, v_cls_202_);
lean_ctor_set(v___x_239_, 1, v___x_235_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
lean_ctor_set_float(v___x_239_, sizeof(void*)*3, v___x_236_);
lean_ctor_set_float(v___x_239_, sizeof(void*)*3 + 8, v___x_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*3 + 16, v___x_237_);
v___x_240_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2));
v___x_241_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v_a_211_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
lean_inc(v_ref_209_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_ref_209_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_PersistentArray_push___redArg(v_traces_230_, v___x_242_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_243_);
v___x_245_ = v___x_232_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_243_);
lean_ctor_set_uint64(v_reuseFailAlloc_253_, sizeof(void*)*1, v_tid_229_);
v___x_245_ = v_reuseFailAlloc_253_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 4, v___x_245_);
v___x_247_ = v___x_227_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_env_217_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_nextMacroScope_218_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_ngen_219_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_auxDeclNGen_220_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_cache_221_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_recordedDeps_222_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_messages_223_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v_infoState_224_);
lean_ctor_set(v_reuseFailAlloc_252_, 9, v_snapshotTasks_225_);
v___x_247_ = v_reuseFailAlloc_252_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_st_ref_put(v___y_207_, v___x_247_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_234_);
v___x_250_ = v___x_213_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_234_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_257_, lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_257_, v_msg_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6));
v___x_284_ = l_Lean_mkCIdent(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Array_mkArray0___redArg();
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30));
v___x_333_ = l_String_toRawSubstring_x27(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_361_ = l_String_toRawSubstring_x27(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82));
v___x_454_ = l_Lean_Name_append(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(lean_object* v_declName_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_declName_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v_all_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v_all_651_ = lean_ctor_get(v_a_473_, 3);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = l_List_lengthTR___redArg(v_all_651_);
v___x_654_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
lean_dec(v___x_653_);
if (v___x_654_ == 0)
{
v___y_634_ = v_a_465_;
v___y_635_ = v_a_466_;
v___y_636_ = v_a_467_;
v___y_637_ = v_a_468_;
v___y_638_ = v_a_469_;
v___y_639_ = v_a_470_;
goto v___jp_633_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_a_473_);
v___x_655_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89);
v___x_656_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_655_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_474_:
{
lean_object* v___x_481_; 
lean_inc(v_a_473_);
v___x_481_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_473_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_n(v_a_482_, 2);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_482_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1));
lean_inc(v_a_482_);
lean_inc(v_a_473_);
v___x_486_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_485_, v_a_473_, v_a_482_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = l_Array_append___redArg(v_a_484_, v_a_487_);
lean_dec(v_a_487_);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6));
lean_inc(v_a_482_);
lean_inc(v_a_473_);
v___x_490_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_489_, v_a_473_, v_a_482_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = l_Array_append___redArg(v___x_488_, v_a_491_);
lean_dec(v_a_491_);
v___x_493_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_473_, v_a_482_, v___y_479_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_toCold_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_608_; 
v_toCold_494_ = lean_ctor_get(v___y_479_, 0);
v_a_495_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_608_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_608_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_608_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_ref_499_; lean_object* v_options_500_; lean_object* v_quotContext_501_; lean_object* v_currMacroScope_502_; lean_object* v_inheritedTraceOptions_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v_hasTrace_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_ref_499_ = lean_ctor_get(v___y_479_, 2);
v_options_500_ = lean_ctor_get(v_toCold_494_, 2);
v_quotContext_501_ = lean_ctor_get(v_toCold_494_, 8);
v_currMacroScope_502_ = lean_ctor_get(v_toCold_494_, 9);
v_inheritedTraceOptions_503_ = lean_ctor_get(v_toCold_494_, 11);
v___x_504_ = 0;
v___x_505_ = l_Lean_SourceInfo_fromRef(v_ref_499_, v___x_504_);
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8));
lean_inc_n(v___x_505_, 30);
v___x_507_ = l_Lean_Syntax_node1(v___x_505_, v___x_506_, v_a_495_);
v___x_508_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10));
v___x_509_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11);
v___x_510_ = l_Lean_Syntax_node2(v___x_505_, v___x_508_, v___x_509_, v___x_507_);
v___x_511_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14));
v___x_512_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16));
v___x_513_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17);
v___x_514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_505_);
lean_ctor_set(v___x_514_, 1, v___x_506_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
lean_inc_ref_n(v___x_514_, 12);
v___x_515_ = l_Lean_Syntax_node7(v___x_505_, v___x_512_, v___x_514_, v___x_514_, v___x_514_, v___x_514_, v___x_514_, v___x_514_, v___x_514_);
v___x_516_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18));
v___x_517_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19));
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21));
v___x_519_ = l_Lean_Syntax_node1(v___x_505_, v___x_518_, v___x_514_);
v___x_520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_505_);
lean_ctor_set(v___x_520_, 1, v___x_516_);
v___x_521_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23));
v___x_522_ = l_Array_append___redArg(v___x_513_, v___x_492_);
lean_dec_ref(v___x_492_);
v___x_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_523_, 0, v___x_505_);
lean_ctor_set(v___x_523_, 1, v___x_506_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25));
v___x_525_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_505_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_Syntax_node2(v___x_505_, v___x_524_, v___x_526_, v___x_510_);
v___x_528_ = l_Lean_Syntax_node2(v___x_505_, v___x_521_, v___x_523_, v___x_527_);
v___x_529_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28));
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29));
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_505_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31);
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33));
lean_inc_n(v_currMacroScope_502_, 2);
lean_inc_n(v_quotContext_501_, 2);
v___x_534_ = l_Lean_addMacroScope(v_quotContext_501_, v___x_533_, v_currMacroScope_502_);
v___x_535_ = lean_box(0);
v___x_536_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35));
v___x_537_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_537_, 0, v___x_505_);
lean_ctor_set(v___x_537_, 1, v___x_532_);
lean_ctor_set(v___x_537_, 2, v___x_534_);
lean_ctor_set(v___x_537_, 3, v___x_536_);
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37));
v___x_539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39));
v___x_540_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40));
v___x_541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_505_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42));
v___x_543_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43);
v___x_544_ = lean_box(0);
v___x_545_ = l_Lean_addMacroScope(v_quotContext_501_, v___x_544_, v_currMacroScope_502_);
v___x_546_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64));
v___x_547_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_547_, 0, v___x_505_);
lean_ctor_set(v___x_547_, 1, v___x_543_);
lean_ctor_set(v___x_547_, 2, v___x_545_);
lean_ctor_set(v___x_547_, 3, v___x_546_);
v___x_548_ = l_Lean_Syntax_node1(v___x_505_, v___x_542_, v___x_547_);
v___x_549_ = l_Lean_Syntax_node2(v___x_505_, v___x_539_, v___x_541_, v___x_548_);
v___x_550_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66));
v___x_551_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67));
v___x_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_505_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69));
v___x_554_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71));
v___x_555_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73));
v___x_556_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74));
v___x_557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_505_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_Syntax_node1(v___x_505_, v___x_555_, v___x_557_);
v___x_559_ = l_Lean_Syntax_node1(v___x_505_, v___x_506_, v___x_558_);
v___x_560_ = l_Lean_Syntax_node1(v___x_505_, v___x_554_, v___x_559_);
v___x_561_ = l_Lean_Syntax_node1(v___x_505_, v___x_553_, v___x_560_);
v___x_562_ = l_Lean_Syntax_node2(v___x_505_, v___x_550_, v___x_552_, v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75));
v___x_564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_505_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_Syntax_node3(v___x_505_, v___x_538_, v___x_549_, v___x_562_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node1(v___x_505_, v___x_506_, v___x_565_);
v___x_567_ = l_Lean_Syntax_node2(v___x_505_, v___x_508_, v___x_537_, v___x_566_);
v___x_568_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78));
v___x_569_ = l_Lean_Syntax_node2(v___x_505_, v___x_568_, v___x_514_, v___x_514_);
v___x_570_ = l_Lean_Syntax_node4(v___x_505_, v___x_529_, v___x_531_, v___x_567_, v___x_569_, v___x_514_);
v___x_571_ = l_Lean_Syntax_node6(v___x_505_, v___x_517_, v___x_519_, v___x_520_, v___x_514_, v___x_514_, v___x_528_, v___x_570_);
v_hasTrace_572_ = lean_ctor_get_uint8(v_options_500_, sizeof(void*)*1);
v___x_573_ = l_Lean_Syntax_node2(v___x_505_, v___x_511_, v___x_515_, v___x_571_);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
v___x_576_ = lean_array_push(v___x_575_, v___x_573_);
if (v_hasTrace_572_ == 0)
{
lean_object* v___x_578_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_576_);
v___x_578_ = v___x_497_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_581_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83);
v___x_582_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_503_, v_options_500_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_584_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_576_);
v___x_584_ = v___x_497_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_576_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_del_object(v___x_497_);
v___x_586_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85);
lean_inc_ref(v___x_576_);
v___x_587_ = lean_array_to_list(v___x_576_);
v___x_588_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(v___x_587_, v___x_535_);
v___x_589_ = l_Lean_MessageData_ofList(v___x_588_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_586_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v___x_580_, v___x_590_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_599_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_576_);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_576_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v___x_576_);
v_a_600_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_591_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_591_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v___x_492_);
v_a_609_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_493_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_493_);
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
else
{
lean_dec_ref(v___x_488_);
lean_dec(v_a_482_);
lean_dec(v_a_473_);
return v___x_490_;
}
}
else
{
lean_dec(v_a_484_);
lean_dec(v_a_482_);
lean_dec(v_a_473_);
return v___x_486_;
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_a_482_);
lean_dec(v_a_473_);
v_a_617_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_483_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_483_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_473_);
v_a_625_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_481_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_481_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
v___jp_633_:
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_InductiveVal_isNested(v_a_473_);
if (v___x_640_ == 0)
{
v___y_475_ = v___y_634_;
v___y_476_ = v___y_635_;
v___y_477_ = v___y_636_;
v___y_478_ = v___y_637_;
v___y_479_ = v___y_638_;
v___y_480_ = v___y_639_;
goto v___jp_474_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_a_473_);
v___x_641_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87);
v___x_642_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_641_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_472_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_472_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed(lean_object* v_declName_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(v_declName_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(lean_object* v_cls_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_682_, v_msg_683_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___boxed(lean_object* v_cls_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(v_cls_692_, v_msg_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(lean_object* v_00_u03b1_702_, lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___boxed(lean_object* v_00_u03b1_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(v_00_u03b1_712_, v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(lean_object* v_msgData_722_, lean_object* v_macroStack_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_722_, v_macroStack_723_, v___y_728_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___boxed(lean_object* v_msgData_732_, lean_object* v_macroStack_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(v_msgData_732_, v_macroStack_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(lean_object* v_as_742_, size_t v_i_743_, size_t v_stop_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_eq(v_i_743_, v_stop_744_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_array_uget_borrowed(v_as_742_, v_i_743_);
lean_inc(v___x_750_);
v___x_751_ = l_Lean_Elab_Command_elabCommand(v___x_750_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; size_t v___x_753_; size_t v___x_754_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_743_, v___x_753_);
v_i_743_ = v___x_754_;
v_b_745_ = v_a_752_;
goto _start;
}
else
{
return v___x_751_;
}
}
else
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_b_745_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0___boxed(lean_object* v_as_757_, lean_object* v_i_758_, lean_object* v_stop_759_, lean_object* v_b_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
size_t v_i_boxed_764_; size_t v_stop_boxed_765_; lean_object* v_res_766_; 
v_i_boxed_764_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_stop_boxed_765_ = lean_unbox_usize(v_stop_759_);
lean_dec(v_stop_759_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_as_757_, v_i_boxed_764_, v_stop_boxed_765_, v_b_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec_ref(v_as_757_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(lean_object* v___x_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_793_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_793_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_793_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_793_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_array_get_size(v_a_772_);
v___x_778_ = lean_box(0);
v___x_779_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
if (v___x_779_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_a_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_778_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_778_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_le(v___x_777_, v___x_777_);
if (v___x_783_ == 0)
{
if (v___x_779_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_a_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_778_);
v___x_785_ = v___x_774_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_778_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_774_);
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_of_nat(v___x_777_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_772_, v___x_787_, v___x_788_, v___x_778_, v___y_768_, v___y_769_);
lean_dec(v_a_772_);
return v___x_789_;
}
}
else
{
size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; 
lean_del_object(v___x_774_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_777_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_772_, v___x_790_, v___x_791_, v___x_778_, v___y_768_, v___y_769_);
lean_dec(v_a_772_);
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_771_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_771_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed(lean_object* v___x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(v___x_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(lean_object* v_declName_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; 
lean_inc(v_declName_807_);
v___x_811_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_811_, 0, v_declName_807_);
v___f_812_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(v___f_812_, 0, v___x_811_);
v___x_813_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_807_, v___f_812_, v_a_808_, v_a_809_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___boxed(lean_object* v_declName_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_declName_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_env_823_; uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_822_ = lean_st_ref_get(v___y_820_);
v_env_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_ref(v_env_823_);
lean_dec(v___x_822_);
v___x_824_ = l_Lean_isInductiveCore(v_env_823_, v_declName_819_);
v___x_825_ = lean_box(v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_827_, v___y_828_);
lean_dec(v___y_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(lean_object* v_declName_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_831_, v___y_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(v_declName_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(uint8_t v_____do__lift_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
if (v_____do__lift_841_ == 0)
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = 1;
v___x_846_ = lean_box(v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
else
{
uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = 0;
v___x_849_ = lean_box(v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v_____do__lift_1654__boxed_855_; lean_object* v_res_856_; 
v_____do__lift_1654__boxed_855_ = lean_unbox(v_____do__lift_851_);
v_res_856_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v_____do__lift_1654__boxed_855_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(lean_object* v_as_857_, size_t v_i_858_, size_t v_stop_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_eq(v_i_858_, v_stop_859_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = 1;
v___x_869_ = lean_array_uget_borrowed(v_as_857_, v_i_858_);
lean_inc(v___x_869_);
v___x_870_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v___x_869_, v___y_861_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_a_871_);
lean_dec(v_a_871_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_box(v___x_868_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_del_object(v___x_873_);
goto v___jp_863_;
}
}
}
else
{
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_890_; 
v_a_881_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_890_ == 0)
{
v___x_883_ = v___x_870_;
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_870_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = lean_unbox(v_a_881_);
lean_dec(v_a_881_);
if (v___x_885_ == 0)
{
lean_del_object(v___x_883_);
goto v___jp_863_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_box(v___x_868_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
lean_ctor_set(v___x_883_, 0, v___x_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
return v___x_870_;
}
}
}
else
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = 0;
v___x_892_ = lean_box(v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
v___jp_863_:
{
size_t v___x_864_; size_t v___x_865_; 
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_858_, v___x_864_);
v_i_858_ = v___x_865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2___boxed(lean_object* v_as_894_, lean_object* v_i_895_, lean_object* v_stop_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
size_t v_i_boxed_900_; size_t v_stop_boxed_901_; lean_object* v_res_902_; 
v_i_boxed_900_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_stop_boxed_901_ = lean_unbox_usize(v_stop_896_);
lean_dec(v_stop_896_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_as_894_, v_i_boxed_900_, v_stop_boxed_901_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec_ref(v_as_894_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v_b_906_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; lean_object* v_a_913_; lean_object* v___x_914_; 
v___x_912_ = lean_box(0);
v_a_913_ = lean_array_uget_borrowed(v_as_903_, v_i_905_);
lean_inc(v_a_913_);
v___x_914_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_a_913_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_914_) == 0)
{
size_t v___x_915_; size_t v___x_916_; 
lean_dec_ref_known(v___x_914_, 1);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_905_, v___x_915_);
v_i_905_ = v___x_916_;
v_b_906_ = v___x_912_;
goto _start;
}
else
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0___boxed(lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
size_t v_sz_boxed_925_; size_t v_i_boxed_926_; lean_object* v_res_927_; 
v_sz_boxed_925_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_926_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_as_918_, v_sz_boxed_925_, v_i_boxed_926_, v_b_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_as_918_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(lean_object* v_declNames_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___y_956_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_array_get_size(v_declNames_928_);
v___x_961_ = lean_nat_dec_lt(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_961_, v_a_929_, v_a_930_);
v___y_956_ = v___x_962_;
goto v___jp_955_;
}
else
{
if (v___x_961_ == 0)
{
goto v___jp_932_;
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_usize_of_nat(v___x_960_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_declNames_928_, v___x_963_, v___x_964_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = lean_unbox(v_a_966_);
lean_dec(v_a_966_);
v___x_968_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_967_, v_a_929_, v_a_930_);
v___y_956_ = v___x_968_;
goto v___jp_955_;
}
else
{
v___y_956_ = v___x_965_;
goto v___jp_955_;
}
}
}
v___jp_932_:
{
uint8_t v___x_933_; lean_object* v___x_934_; size_t v_sz_935_; size_t v___x_936_; lean_object* v___x_937_; 
v___x_933_ = 1;
v___x_934_ = lean_box(0);
v_sz_935_ = lean_array_size(v_declNames_928_);
v___x_936_ = ((size_t)0ULL);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_declNames_928_, v_sz_935_, v___x_936_, v___x_934_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_945_; 
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_937_, 0);
lean_dec(v_unused_946_);
v___x_939_ = v___x_937_;
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
else
{
lean_dec(v___x_937_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_box(v___x_933_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_937_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_937_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
v___jp_955_:
{
if (lean_obj_tag(v___y_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; 
v_a_957_ = lean_ctor_get(v___y_956_, 0);
v___x_958_ = lean_unbox(v_a_957_);
if (v___x_958_ == 0)
{
return v___y_956_;
}
else
{
lean_dec_ref_known(v___y_956_, 1);
goto v___jp_932_;
}
}
else
{
return v___y_956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed(lean_object* v_declNames_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(v_declNames_969_, v_a_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec_ref(v_declNames_969_);
return v_res_973_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(3244286355u);
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1028_ = l_Lean_Name_num___override(v___x_1027_, v___x_1026_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1031_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1032_ = l_Lean_Name_str___override(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1035_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1036_ = l_Lean_Name_str___override(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_unsigned_to_nat(2u);
v___x_1038_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1039_ = l_Lean_Name_num___override(v___x_1038_, v___x_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6));
v___x_1042_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1043_ = l_Lean_Elab_registerDerivingHandler(v___x_1041_, v___x_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref_known(v___x_1043_, 1);
v___x_1044_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_1045_ = 0;
v___x_1046_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1047_ = l_Lean_registerTraceClass(v___x_1044_, v___x_1045_, v___x_1046_);
return v___x_1047_;
}
else
{
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2____boxed(lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
return v_res_1049_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_LawfulBEq(uint8_t builtin) {
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
res = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_LawfulBEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_LawfulBEq(uint8_t builtin) {
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
res = runtime_initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
}
#ifdef __cplusplus
}
#endif
