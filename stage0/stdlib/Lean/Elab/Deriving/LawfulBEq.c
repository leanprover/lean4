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
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(lean_object* v_opts_15_, lean_object* v_opt_16_){
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_15_ = stack[0].m_obj;
lean_object* v_opt_16_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_15_, v_opt_16_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(lean_object* v_opts_26_, lean_object* v_opt_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_26_, v_opt_27_);
lean_dec_ref(v_opt_27_);
lean_dec_ref(v_opts_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_box(1);
v___x_31_ = l_Lean_MessageData_ofFormat(v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2));
v___x_36_ = l_Lean_MessageData_ofFormat(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
return v_x_37_;
}
else
{
lean_object* v_head_39_; lean_object* v_tail_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_62_; 
v_head_39_ = lean_ctor_get(v_x_38_, 0);
v_tail_40_ = lean_ctor_get(v_x_38_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_x_38_);
if (v_isSharedCheck_62_ == 0)
{
v___x_42_ = v_x_38_;
v_isShared_43_ = v_isSharedCheck_62_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_tail_40_);
lean_inc(v_head_39_);
lean_dec(v_x_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_62_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_before_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_60_; 
v_before_44_ = lean_ctor_get(v_head_39_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_head_39_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v_head_39_, 1);
lean_dec(v_unused_61_);
v___x_46_ = v_head_39_;
v_isShared_47_ = v_isSharedCheck_60_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_before_44_);
lean_dec(v_head_39_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_60_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 7);
lean_ctor_set(v___x_46_, 1, v___x_48_);
lean_ctor_set(v___x_46_, 0, v_x_37_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_x_37_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___x_48_);
v___x_50_ = v_reuseFailAlloc_59_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3);
if (v_isShared_43_ == 0)
{
lean_ctor_set_tag(v___x_42_, 7);
lean_ctor_set(v___x_42_, 1, v___x_51_);
lean_ctor_set(v___x_42_, 0, v___x_50_);
v___x_53_ = v___x_42_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_51_);
v___x_53_ = v_reuseFailAlloc_58_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = l_Lean_MessageData_ofSyntax(v_before_44_);
v___x_55_ = l_Lean_indentD(v___x_54_);
v___x_56_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_53_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v_x_37_ = v___x_56_;
v_x_38_ = v_tail_40_;
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
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1));
v___x_67_ = l_Lean_MessageData_ofFormat(v___x_66_);
return v___x_67_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(lean_object* v_msgData_68_, lean_object* v_macroStack_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_72_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_70_);
v___x_73_ = l_Lean_Elab_pp_macroStack;
v___x_74_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v___x_72_, v___x_73_);
lean_dec_ref(v___x_72_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v_macroStack_69_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_msgData_68_);
return v___x_75_;
}
else
{
if (lean_obj_tag(v_macroStack_69_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v_msgData_68_);
return v___x_76_;
}
else
{
lean_object* v_head_77_; lean_object* v_after_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_93_; 
v_head_77_ = lean_ctor_get(v_macroStack_69_, 0);
lean_inc(v_head_77_);
v_after_78_ = lean_ctor_get(v_head_77_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_head_77_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_head_77_, 0);
lean_dec(v_unused_94_);
v___x_80_ = v_head_77_;
v_isShared_81_ = v_isSharedCheck_93_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_after_78_);
lean_dec(v_head_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_93_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 7);
lean_ctor_set(v___x_80_, 1, v___x_82_);
lean_ctor_set(v___x_80_, 0, v_msgData_68_);
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_msgData_68_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_92_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_msgData_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_85_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2);
v___x_86_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Lean_MessageData_ofSyntax(v_after_78_);
v___x_88_ = l_Lean_indentD(v___x_87_);
v_msgData_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_89_, 0, v___x_86_);
lean_ctor_set(v_msgData_89_, 1, v___x_88_);
v___x_90_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(v_msgData_89_, v_macroStack_69_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_68_ = stack[0].m_obj;
lean_object* v_macroStack_69_ = stack[1].m_obj;
lean_object* v___y_70_ = stack[2].m_obj;
lean_object* v_res_95_;
v_res_95_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_68_, v_macroStack_69_, v___y_70_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_96_, lean_object* v_macroStack_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_96_, v_macroStack_97_, v___y_98_);
lean_dec_ref(v___y_98_);
return v_res_100_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_env_108_; uint8_t v___x_109_; lean_object* v_env_110_; lean_object* v___x_111_; lean_object* v_toCold_112_; lean_object* v_mctx_113_; lean_object* v_lctx_114_; lean_object* v_options_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_107_);
v___x_109_ = 0;
v_env_110_ = l_Lean_Environment_setRecordingDeps(v_env_108_, v___x_109_);
v___x_111_ = lean_st_ref_get(v___y_103_);
v_toCold_112_ = lean_ctor_get(v___y_104_, 0);
v_mctx_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_mctx_113_);
lean_dec(v___x_111_);
v_lctx_114_ = lean_ctor_get(v___y_102_, 2);
v_options_115_ = lean_ctor_get(v_toCold_112_, 2);
lean_inc_ref(v_options_115_);
lean_inc_ref(v_lctx_114_);
v___x_116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_116_, 0, v_env_110_);
lean_ctor_set(v___x_116_, 1, v_mctx_113_);
lean_ctor_set(v___x_116_, 2, v_lctx_114_);
lean_ctor_set(v___x_116_, 3, v_options_115_);
v___x_117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_msgData_101_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_101_ = stack[0].m_obj;
lean_object* v___y_102_ = stack[1].m_obj;
lean_object* v___y_103_ = stack[2].m_obj;
lean_object* v___y_104_ = stack[3].m_obj;
lean_object* v___y_105_ = stack[4].m_obj;
lean_object* v_res_119_;
v_res_119_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2___boxed(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msgData_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(lean_object* v_msg_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_ref_135_; lean_object* v_macroStack_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v_ref_135_ = lean_ctor_get(v___y_132_, 2);
v_macroStack_136_ = lean_ctor_get(v___y_128_, 1);
v___x_137_ = l_Lean_Elab_getBetterRef(v_ref_135_, v_macroStack_136_);
v___x_138_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_127_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
lean_inc(v_macroStack_136_);
v___x_140_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_a_139_, v_macroStack_136_, v___y_132_);
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_137_);
lean_ctor_set(v___x_145_, 1, v_a_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 1);
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_127_ = stack[0].m_obj;
lean_object* v___y_128_ = stack[1].m_obj;
lean_object* v___y_129_ = stack[2].m_obj;
lean_object* v___y_130_ = stack[3].m_obj;
lean_object* v___y_131_ = stack[4].m_obj;
lean_object* v___y_132_ = stack[5].m_obj;
lean_object* v___y_133_ = stack[6].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg___boxed(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_159_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0));
v___x_162_ = l_Lean_stringToMessageData(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2));
v___x_165_ = l_Lean_stringToMessageData(v___x_164_);
return v___x_165_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(lean_object* v_constName_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_env_175_; lean_object* v___x_176_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
lean_inc(v_constName_166_);
v___x_176_ = l_Lean_isInductiveCore_x3f(v_env_175_, v_constName_166_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_177_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1);
v___x_178_ = 0;
v___x_179_ = l_Lean_MessageData_ofConstName(v_constName_166_, v___x_178_);
v___x_180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_177_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3);
v___x_182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_182_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_183_;
}
else
{
lean_object* v_val_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec(v_constName_166_);
v_val_184_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_176_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_val_184_);
lean_dec(v___x_176_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 0);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_val_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_166_ = stack[0].m_obj;
lean_object* v___y_167_ = stack[1].m_obj;
lean_object* v___y_168_ = stack[2].m_obj;
lean_object* v___y_169_ = stack[3].m_obj;
lean_object* v___y_170_ = stack[4].m_obj;
lean_object* v___y_171_ = stack[5].m_obj;
lean_object* v___y_172_ = stack[6].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_constName_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___boxed(lean_object* v_constName_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_constName_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_201_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_202_; double v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_float_of_nat(v___x_202_);
return v___x_203_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(lean_object* v_cls_207_, lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_261_; 
v_ref_214_ = lean_ctor_get(v___y_211_, 2);
v___x_215_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_261_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_261_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_261_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v_traceState_221_; lean_object* v_env_222_; lean_object* v_nextMacroScope_223_; lean_object* v_ngen_224_; lean_object* v_auxDeclNGen_225_; lean_object* v_cache_226_; lean_object* v_recordedDeps_227_; lean_object* v_messages_228_; lean_object* v_infoState_229_; lean_object* v_snapshotTasks_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_260_; 
v___x_220_ = lean_st_ref_take(v___y_212_);
v_traceState_221_ = lean_ctor_get(v___x_220_, 4);
v_env_222_ = lean_ctor_get(v___x_220_, 0);
v_nextMacroScope_223_ = lean_ctor_get(v___x_220_, 1);
v_ngen_224_ = lean_ctor_get(v___x_220_, 2);
v_auxDeclNGen_225_ = lean_ctor_get(v___x_220_, 3);
v_cache_226_ = lean_ctor_get(v___x_220_, 5);
v_recordedDeps_227_ = lean_ctor_get(v___x_220_, 6);
v_messages_228_ = lean_ctor_get(v___x_220_, 7);
v_infoState_229_ = lean_ctor_get(v___x_220_, 8);
v_snapshotTasks_230_ = lean_ctor_get(v___x_220_, 9);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_260_ == 0)
{
v___x_232_ = v___x_220_;
v_isShared_233_ = v_isSharedCheck_260_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snapshotTasks_230_);
lean_inc(v_infoState_229_);
lean_inc(v_messages_228_);
lean_inc(v_recordedDeps_227_);
lean_inc(v_cache_226_);
lean_inc(v_traceState_221_);
lean_inc(v_auxDeclNGen_225_);
lean_inc(v_ngen_224_);
lean_inc(v_nextMacroScope_223_);
lean_inc(v_env_222_);
lean_dec(v___x_220_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_260_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint64_t v_tid_234_; lean_object* v_traces_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_259_; 
v_tid_234_ = lean_ctor_get_uint64(v_traceState_221_, sizeof(void*)*1);
v_traces_235_ = lean_ctor_get(v_traceState_221_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_traceState_221_);
if (v_isSharedCheck_259_ == 0)
{
v___x_237_ = v_traceState_221_;
v_isShared_238_ = v_isSharedCheck_259_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_traces_235_);
lean_dec(v_traceState_221_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_259_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; double v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_box(0);
v___x_241_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0);
v___x_242_ = 0;
v___x_243_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_244_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_244_, 0, v_cls_207_);
lean_ctor_set(v___x_244_, 1, v___x_240_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
lean_ctor_set_float(v___x_244_, sizeof(void*)*3, v___x_241_);
lean_ctor_set_float(v___x_244_, sizeof(void*)*3 + 8, v___x_241_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*3 + 16, v___x_242_);
v___x_245_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2));
v___x_246_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v_a_216_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
lean_inc(v_ref_214_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_ref_214_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_PersistentArray_push___redArg(v_traces_235_, v___x_247_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_248_);
v___x_250_ = v___x_237_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_248_);
lean_ctor_set_uint64(v_reuseFailAlloc_258_, sizeof(void*)*1, v_tid_234_);
v___x_250_ = v_reuseFailAlloc_258_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 4, v___x_250_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_env_222_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextMacroScope_223_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_ngen_224_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_auxDeclNGen_225_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v_cache_226_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v_recordedDeps_227_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v_messages_228_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_infoState_229_);
lean_ctor_set(v_reuseFailAlloc_257_, 9, v_snapshotTasks_230_);
v___x_252_ = v_reuseFailAlloc_257_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_st_ref_put(v___y_212_, v___x_252_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_239_);
v___x_255_ = v___x_218_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_239_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_207_ = stack[0].m_obj;
lean_object* v_msg_208_ = stack[1].m_obj;
lean_object* v___y_209_ = stack[2].m_obj;
lean_object* v___y_210_ = stack[3].m_obj;
lean_object* v___y_211_ = stack[4].m_obj;
lean_object* v___y_212_ = stack[5].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_207_, v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_263_, lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_263_, v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6));
v___x_290_ = l_Lean_mkCIdent(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Array_mkArray0___redArg();
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30));
v___x_339_ = l_String_toRawSubstring_x27(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_367_ = l_String_toRawSubstring_x27(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82));
v___x_460_ = l_Lean_Name_append(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(lean_object* v_declName_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_declName_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v_all_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_all_657_ = lean_ctor_get(v_a_479_, 3);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = l_List_lengthTR___redArg(v_all_657_);
v___x_660_ = lean_nat_dec_lt(v___x_658_, v___x_659_);
lean_dec(v___x_659_);
if (v___x_660_ == 0)
{
v___y_640_ = v_a_471_;
v___y_641_ = v_a_472_;
v___y_642_ = v_a_473_;
v___y_643_ = v_a_474_;
v___y_644_ = v_a_475_;
v___y_645_ = v_a_476_;
goto v___jp_639_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_a_479_);
v___x_661_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89);
v___x_662_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_661_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
v___jp_480_:
{
lean_object* v___x_487_; 
lean_inc(v_a_479_);
v___x_487_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_479_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc_n(v_a_488_, 2);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_488_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1));
lean_inc(v_a_488_);
lean_inc(v_a_479_);
v___x_492_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_491_, v_a_479_, v_a_488_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v___x_494_ = l_Array_append___redArg(v_a_490_, v_a_493_);
lean_dec(v_a_493_);
v___x_495_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6));
lean_inc(v_a_488_);
lean_inc(v_a_479_);
v___x_496_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_495_, v_a_479_, v_a_488_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = l_Array_append___redArg(v___x_494_, v_a_497_);
lean_dec(v_a_497_);
v___x_499_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_479_, v_a_488_, v___y_485_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_toCold_500_; lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_614_; 
v_toCold_500_ = lean_ctor_get(v___y_485_, 0);
v_a_501_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_614_ == 0)
{
v___x_503_ = v___x_499_;
v_isShared_504_ = v_isSharedCheck_614_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_614_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_ref_505_; lean_object* v_options_506_; lean_object* v_quotContext_507_; lean_object* v_currMacroScope_508_; lean_object* v_inheritedTraceOptions_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v_hasTrace_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_ref_505_ = lean_ctor_get(v___y_485_, 2);
v_options_506_ = lean_ctor_get(v_toCold_500_, 2);
v_quotContext_507_ = lean_ctor_get(v_toCold_500_, 8);
v_currMacroScope_508_ = lean_ctor_get(v_toCold_500_, 9);
v_inheritedTraceOptions_509_ = lean_ctor_get(v_toCold_500_, 11);
v___x_510_ = 0;
v___x_511_ = l_Lean_SourceInfo_fromRef(v_ref_505_, v___x_510_);
v___x_512_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8));
lean_inc_n(v___x_511_, 30);
v___x_513_ = l_Lean_Syntax_node1(v___x_511_, v___x_512_, v_a_501_);
v___x_514_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10));
v___x_515_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11);
v___x_516_ = l_Lean_Syntax_node2(v___x_511_, v___x_514_, v___x_515_, v___x_513_);
v___x_517_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14));
v___x_518_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16));
v___x_519_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___x_511_);
lean_ctor_set(v___x_520_, 1, v___x_512_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
lean_inc_ref_n(v___x_520_, 12);
v___x_521_ = l_Lean_Syntax_node7(v___x_511_, v___x_518_, v___x_520_, v___x_520_, v___x_520_, v___x_520_, v___x_520_, v___x_520_, v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18));
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19));
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21));
v___x_525_ = l_Lean_Syntax_node1(v___x_511_, v___x_524_, v___x_520_);
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_511_);
lean_ctor_set(v___x_526_, 1, v___x_522_);
v___x_527_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23));
v___x_528_ = l_Array_append___redArg(v___x_519_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_511_);
lean_ctor_set(v___x_529_, 1, v___x_512_);
lean_ctor_set(v___x_529_, 2, v___x_528_);
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25));
v___x_531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26));
v___x_532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_511_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_Syntax_node2(v___x_511_, v___x_530_, v___x_532_, v___x_516_);
v___x_534_ = l_Lean_Syntax_node2(v___x_511_, v___x_527_, v___x_529_, v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28));
v___x_536_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29));
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_511_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31);
v___x_539_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33));
lean_inc_n(v_currMacroScope_508_, 2);
lean_inc_n(v_quotContext_507_, 2);
v___x_540_ = l_Lean_addMacroScope(v_quotContext_507_, v___x_539_, v_currMacroScope_508_);
v___x_541_ = lean_box(0);
v___x_542_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35));
v___x_543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_543_, 0, v___x_511_);
lean_ctor_set(v___x_543_, 1, v___x_538_);
lean_ctor_set(v___x_543_, 2, v___x_540_);
lean_ctor_set(v___x_543_, 3, v___x_542_);
v___x_544_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37));
v___x_545_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39));
v___x_546_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40));
v___x_547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_511_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42));
v___x_549_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43);
v___x_550_ = lean_box(0);
v___x_551_ = l_Lean_addMacroScope(v_quotContext_507_, v___x_550_, v_currMacroScope_508_);
v___x_552_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64));
v___x_553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_553_, 0, v___x_511_);
lean_ctor_set(v___x_553_, 1, v___x_549_);
lean_ctor_set(v___x_553_, 2, v___x_551_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
v___x_554_ = l_Lean_Syntax_node1(v___x_511_, v___x_548_, v___x_553_);
v___x_555_ = l_Lean_Syntax_node2(v___x_511_, v___x_545_, v___x_547_, v___x_554_);
v___x_556_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66));
v___x_557_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67));
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_511_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69));
v___x_560_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71));
v___x_561_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73));
v___x_562_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74));
v___x_563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_511_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = l_Lean_Syntax_node1(v___x_511_, v___x_561_, v___x_563_);
v___x_565_ = l_Lean_Syntax_node1(v___x_511_, v___x_512_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node1(v___x_511_, v___x_560_, v___x_565_);
v___x_567_ = l_Lean_Syntax_node1(v___x_511_, v___x_559_, v___x_566_);
v___x_568_ = l_Lean_Syntax_node2(v___x_511_, v___x_556_, v___x_558_, v___x_567_);
v___x_569_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75));
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_511_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_Syntax_node3(v___x_511_, v___x_544_, v___x_555_, v___x_568_, v___x_570_);
v___x_572_ = l_Lean_Syntax_node1(v___x_511_, v___x_512_, v___x_571_);
v___x_573_ = l_Lean_Syntax_node2(v___x_511_, v___x_514_, v___x_543_, v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78));
v___x_575_ = l_Lean_Syntax_node2(v___x_511_, v___x_574_, v___x_520_, v___x_520_);
v___x_576_ = l_Lean_Syntax_node4(v___x_511_, v___x_535_, v___x_537_, v___x_573_, v___x_575_, v___x_520_);
v___x_577_ = l_Lean_Syntax_node6(v___x_511_, v___x_523_, v___x_525_, v___x_526_, v___x_520_, v___x_520_, v___x_534_, v___x_576_);
v_hasTrace_578_ = lean_ctor_get_uint8(v_options_506_, sizeof(void*)*1);
v___x_579_ = l_Lean_Syntax_node2(v___x_511_, v___x_517_, v___x_521_, v___x_577_);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_array_push(v___x_581_, v___x_579_);
if (v_hasTrace_578_ == 0)
{
lean_object* v___x_584_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_582_);
v___x_584_ = v___x_503_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
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
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_587_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83);
v___x_588_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_509_, v_options_506_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_582_);
v___x_590_ = v___x_503_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_582_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_503_);
v___x_592_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85);
lean_inc_ref(v___x_582_);
v___x_593_ = lean_array_to_list(v___x_582_);
v___x_594_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(v___x_593_, v___x_541_);
v___x_595_ = l_Lean_MessageData_ofList(v___x_594_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_592_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v___x_586_, v___x_596_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_605_);
v___x_599_ = v___x_597_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_dec(v___x_597_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_582_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_582_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v___x_582_);
v_a_606_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_597_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_597_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v___x_498_);
v_a_615_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_499_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_499_);
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
else
{
lean_dec_ref(v___x_494_);
lean_dec(v_a_488_);
lean_dec(v_a_479_);
return v___x_496_;
}
}
else
{
lean_dec(v_a_490_);
lean_dec(v_a_488_);
lean_dec(v_a_479_);
return v___x_492_;
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_a_488_);
lean_dec(v_a_479_);
v_a_623_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_489_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_489_);
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
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_479_);
v_a_631_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_487_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_487_);
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
v___jp_639_:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_InductiveVal_isNested(v_a_479_);
if (v___x_646_ == 0)
{
v___y_481_ = v___y_640_;
v___y_482_ = v___y_641_;
v___y_483_ = v___y_642_;
v___y_484_ = v___y_643_;
v___y_485_ = v___y_644_;
v___y_486_ = v___y_645_;
goto v___jp_480_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_479_);
v___x_647_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87);
v___x_648_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_647_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_a_671_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_478_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_478_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_470_ = stack[0].m_obj;
lean_object* v_a_471_ = stack[1].m_obj;
lean_object* v_a_472_ = stack[2].m_obj;
lean_object* v_a_473_ = stack[3].m_obj;
lean_object* v_a_474_ = stack[4].m_obj;
lean_object* v_a_475_ = stack[5].m_obj;
lean_object* v_a_476_ = stack[6].m_obj;
lean_object* v_res_679_;
v_res_679_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(v_declName_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed(lean_object* v_declName_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(v_declName_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_688_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(lean_object* v_cls_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_689_, v_msg_690_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
return v___x_698_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_689_ = stack[0].m_obj;
lean_object* v_msg_690_ = stack[1].m_obj;
lean_object* v___y_691_ = stack[2].m_obj;
lean_object* v___y_692_ = stack[3].m_obj;
lean_object* v___y_693_ = stack[4].m_obj;
lean_object* v___y_694_ = stack[5].m_obj;
lean_object* v___y_695_ = stack[6].m_obj;
lean_object* v___y_696_ = stack[7].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(v_cls_689_, v_msg_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___boxed(lean_object* v_cls_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(v_cls_700_, v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_709_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(lean_object* v_00_u03b1_710_, lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_711_ = stack[1].m_obj;
lean_object* v___y_712_ = stack[2].m_obj;
lean_object* v___y_713_ = stack[3].m_obj;
lean_object* v___y_714_ = stack[4].m_obj;
lean_object* v___y_715_ = stack[5].m_obj;
lean_object* v___y_716_ = stack[6].m_obj;
lean_object* v___y_717_ = stack[7].m_obj;
lean_object* v_res_720_;
v_res_720_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(lean_box(0), v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___boxed(lean_object* v_00_u03b1_721_, lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(v_00_u03b1_721_, v_msg_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_730_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(lean_object* v_msgData_731_, lean_object* v_macroStack_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_731_, v_macroStack_732_, v___y_737_);
return v___x_740_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_731_ = stack[0].m_obj;
lean_object* v_macroStack_732_ = stack[1].m_obj;
lean_object* v___y_733_ = stack[2].m_obj;
lean_object* v___y_734_ = stack[3].m_obj;
lean_object* v___y_735_ = stack[4].m_obj;
lean_object* v___y_736_ = stack[5].m_obj;
lean_object* v___y_737_ = stack[6].m_obj;
lean_object* v___y_738_ = stack[7].m_obj;
lean_object* v_res_741_;
v_res_741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(v_msgData_731_, v_macroStack_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___boxed(lean_object* v_msgData_742_, lean_object* v_macroStack_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(v_msgData_742_, v_macroStack_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(lean_object* v_as_752_, size_t v_i_753_, size_t v_stop_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = lean_usize_dec_eq(v_i_753_, v_stop_754_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_array_uget_borrowed(v_as_752_, v_i_753_);
lean_inc(v___x_760_);
v___x_761_ = l_Lean_Elab_Command_elabCommand(v___x_760_, v___y_756_, v___y_757_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; size_t v___x_763_; size_t v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_753_, v___x_763_);
v_i_753_ = v___x_764_;
v_b_755_ = v_a_762_;
goto _start;
}
else
{
return v___x_761_;
}
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_755_);
return v___x_766_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_752_ = stack[0].m_obj;
size_t v_i_753_ = stack[1].m_num;
size_t v_stop_754_ = stack[2].m_num;
lean_object* v_b_755_ = stack[3].m_obj;
lean_object* v___y_756_ = stack[4].m_obj;
lean_object* v___y_757_ = stack[5].m_obj;
lean_object* v_res_767_;
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_as_752_, v_i_753_, v_stop_754_, v_b_755_, v___y_756_, v___y_757_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0___boxed(lean_object* v_as_768_, lean_object* v_i_769_, lean_object* v_stop_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
size_t v_i_boxed_775_; size_t v_stop_boxed_776_; lean_object* v_res_777_; 
v_i_boxed_775_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_stop_boxed_776_ = lean_unbox_usize(v_stop_770_);
lean_dec(v_stop_770_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_as_768_, v_i_boxed_775_, v_stop_boxed_776_, v_b_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_as_768_);
return v_res_777_;
}
}
lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(lean_object* v___x_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_778_, v___y_779_, v___y_780_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_804_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_804_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_804_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_804_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_array_get_size(v_a_783_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v_a_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_789_);
v___x_792_ = v___x_785_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_789_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
uint8_t v___x_794_; 
v___x_794_ = lean_nat_dec_le(v___x_788_, v___x_788_);
if (v___x_794_ == 0)
{
if (v___x_790_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_a_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_789_);
v___x_796_ = v___x_785_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_789_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_785_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_788_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_783_, v___x_798_, v___x_799_, v___x_789_, v___y_779_, v___y_780_);
lean_dec(v_a_783_);
return v___x_800_;
}
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_785_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_788_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_783_, v___x_801_, v___x_802_, v___x_789_, v___y_779_, v___y_780_);
lean_dec(v_a_783_);
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_782_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_782_);
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
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_778_ = stack[0].m_obj;
lean_object* v___y_779_ = stack[1].m_obj;
lean_object* v___y_780_ = stack[2].m_obj;
lean_object* v_res_813_;
v_res_813_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(v___x_778_, v___y_779_, v___y_780_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed(lean_object* v___x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(v___x_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_818_;
}
}
lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(lean_object* v_declName_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_825_; 
lean_inc(v_declName_819_);
v___x_823_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_823_, 0, v_declName_819_);
v___f_824_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(v___f_824_, 0, v___x_823_);
v___x_825_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_819_, v___f_824_, v_a_820_, v_a_821_);
return v___x_825_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_819_ = stack[0].m_obj;
lean_object* v_a_820_ = stack[1].m_obj;
lean_object* v_a_821_ = stack[2].m_obj;
lean_object* v_res_826_;
v_res_826_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_declName_819_, v_a_820_, v_a_821_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___boxed(lean_object* v_declName_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_declName_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_831_;
}
}
lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_env_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_835_ = lean_st_ref_get(v___y_833_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_env_836_);
lean_dec(v___x_835_);
v___x_837_ = l_Lean_isInductiveCore(v_env_836_, v_declName_832_);
v___x_838_ = lean_box(v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_832_ = stack[0].m_obj;
lean_object* v___y_833_ = stack[1].m_obj;
lean_object* v_res_840_;
v_res_840_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_832_, v___y_833_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_841_, v___y_842_);
lean_dec(v___y_842_);
return v_res_844_;
}
}
lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(lean_object* v_declName_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_845_, v___y_847_);
return v___x_849_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_845_ = stack[0].m_obj;
lean_object* v___y_846_ = stack[1].m_obj;
lean_object* v___y_847_ = stack[2].m_obj;
lean_object* v_res_850_;
v_res_850_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(v_declName_845_, v___y_846_, v___y_847_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(v_declName_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_855_;
}
}
lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(uint8_t v_____do__lift_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
if (v_____do__lift_856_ == 0)
{
uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = 1;
v___x_861_ = lean_box(v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
else
{
uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = 0;
v___x_864_ = lean_box(v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_856_ = stack[0].m_num;
lean_object* v___y_857_ = stack[1].m_obj;
lean_object* v___y_858_ = stack[2].m_obj;
lean_object* v_res_866_;
v_res_866_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v_____do__lift_856_, v___y_857_, v___y_858_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v_____do__lift_1669__boxed_871_; lean_object* v_res_872_; 
v_____do__lift_1669__boxed_871_ = lean_unbox(v_____do__lift_867_);
v_res_872_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v_____do__lift_1669__boxed_871_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_872_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(lean_object* v_as_873_, size_t v_i_874_, size_t v_stop_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_eq(v_i_874_, v_stop_875_);
if (v___x_883_ == 0)
{
uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = 1;
v___x_885_ = lean_array_uget_borrowed(v_as_873_, v_i_874_);
lean_inc(v___x_885_);
v___x_886_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v___x_885_, v___y_877_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_896_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_896_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; 
v___x_891_ = lean_unbox(v_a_887_);
lean_dec(v_a_887_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_box(v___x_884_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
else
{
lean_del_object(v___x_889_);
goto v___jp_879_;
}
}
}
else
{
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_906_; 
v_a_897_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_906_ == 0)
{
v___x_899_ = v___x_886_;
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_886_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; 
v___x_901_ = lean_unbox(v_a_897_);
lean_dec(v_a_897_);
if (v___x_901_ == 0)
{
lean_del_object(v___x_899_);
goto v___jp_879_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_box(v___x_884_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 0);
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
}
else
{
return v___x_886_;
}
}
}
else
{
uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = 0;
v___x_908_ = lean_box(v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
v___jp_879_:
{
size_t v___x_880_; size_t v___x_881_; 
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_874_, v___x_880_);
v_i_874_ = v___x_881_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_873_ = stack[0].m_obj;
size_t v_i_874_ = stack[1].m_num;
size_t v_stop_875_ = stack[2].m_num;
lean_object* v___y_876_ = stack[3].m_obj;
lean_object* v___y_877_ = stack[4].m_obj;
lean_object* v_res_910_;
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_as_873_, v_i_874_, v_stop_875_, v___y_876_, v___y_877_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2___boxed(lean_object* v_as_911_, lean_object* v_i_912_, lean_object* v_stop_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_i_boxed_917_; size_t v_stop_boxed_918_; lean_object* v_res_919_; 
v_i_boxed_917_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_stop_boxed_918_ = lean_unbox_usize(v_stop_913_);
lean_dec(v_stop_913_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_as_911_, v_i_boxed_917_, v_stop_boxed_918_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_as_911_);
return v_res_919_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(lean_object* v_as_920_, size_t v_sz_921_, size_t v_i_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = lean_usize_dec_lt(v_i_922_, v_sz_921_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v_b_923_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
v_a_930_ = lean_array_uget_borrowed(v_as_920_, v_i_922_);
lean_inc(v_a_930_);
v___x_931_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_a_930_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_931_) == 0)
{
size_t v___x_932_; size_t v___x_933_; 
lean_dec_ref_known(v___x_931_, 1);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_922_, v___x_932_);
v_i_922_ = v___x_933_;
v_b_923_ = v___x_929_;
goto _start;
}
else
{
return v___x_931_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_920_ = stack[0].m_obj;
size_t v_sz_921_ = stack[1].m_num;
size_t v_i_922_ = stack[2].m_num;
lean_object* v_b_923_ = stack[3].m_obj;
lean_object* v___y_924_ = stack[4].m_obj;
lean_object* v___y_925_ = stack[5].m_obj;
lean_object* v_res_935_;
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_as_920_, v_sz_921_, v_i_922_, v_b_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_935_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0___boxed(lean_object* v_as_936_, lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
size_t v_sz_boxed_943_; size_t v_i_boxed_944_; lean_object* v_res_945_; 
v_sz_boxed_943_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_944_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_as_936_, v_sz_boxed_943_, v_i_boxed_944_, v_b_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v_as_936_);
return v_res_945_;
}
}
lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(lean_object* v_declNames_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___y_974_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_array_get_size(v_declNames_946_);
v___x_979_ = lean_nat_dec_lt(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_979_, v_a_947_, v_a_948_);
v___y_974_ = v___x_980_;
goto v___jp_973_;
}
else
{
if (v___x_979_ == 0)
{
goto v___jp_950_;
}
else
{
size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((size_t)0ULL);
v___x_982_ = lean_usize_of_nat(v___x_978_);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_declNames_946_, v___x_981_, v___x_982_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = lean_unbox(v_a_984_);
lean_dec(v_a_984_);
v___x_986_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_985_, v_a_947_, v_a_948_);
v___y_974_ = v___x_986_;
goto v___jp_973_;
}
else
{
v___y_974_ = v___x_983_;
goto v___jp_973_;
}
}
}
v___jp_950_:
{
uint8_t v___x_951_; lean_object* v___x_952_; size_t v_sz_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_951_ = 1;
v___x_952_ = lean_box(0);
v_sz_953_ = lean_array_size(v_declNames_946_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_declNames_946_, v_sz_953_, v___x_954_, v___x_952_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_964_);
v___x_957_ = v___x_955_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_dec(v___x_955_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_box(v___x_951_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_955_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_955_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
v___jp_973_:
{
if (lean_obj_tag(v___y_974_) == 0)
{
lean_object* v_a_975_; uint8_t v___x_976_; 
v_a_975_ = lean_ctor_get(v___y_974_, 0);
v___x_976_ = lean_unbox(v_a_975_);
if (v___x_976_ == 0)
{
return v___y_974_;
}
else
{
lean_dec_ref_known(v___y_974_, 1);
goto v___jp_950_;
}
}
else
{
return v___y_974_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_946_ = stack[0].m_obj;
lean_object* v_a_947_ = stack[1].m_obj;
lean_object* v_a_948_ = stack[2].m_obj;
lean_object* v_res_987_;
v_res_987_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(v_declNames_946_, v_a_947_, v_a_948_);
stack->m_obj
 = v_res_987_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed(lean_object* v_declNames_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(v_declNames_988_, v_a_989_, v_a_990_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec_ref(v_declNames_988_);
return v_res_992_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = lean_unsigned_to_nat(3244286355u);
v___x_1046_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1047_ = l_Lean_Name_num___override(v___x_1046_, v___x_1045_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1050_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1051_ = l_Lean_Name_str___override(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1054_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1055_ = l_Lean_Name_str___override(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_unsigned_to_nat(2u);
v___x_1057_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1058_ = l_Lean_Name_num___override(v___x_1057_, v___x_1056_);
return v___x_1058_;
}
}
lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6));
v___x_1061_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1062_ = l_Lean_Elab_registerDerivingHandler(v___x_1060_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref_known(v___x_1062_, 1);
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_1064_ = 0;
v___x_1065_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1066_ = l_Lean_registerTraceClass(v___x_1063_, v___x_1064_, v___x_1065_);
return v___x_1066_;
}
else
{
return v___x_1062_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1067_;
v_res_1067_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2____boxed(lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
return v_res_1069_;
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
