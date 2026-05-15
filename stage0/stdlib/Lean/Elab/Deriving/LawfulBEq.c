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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LawfulBEq"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 227, 222, 64, 229, 226, 161)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 216, 42, 178, 87, 188, 183, 65)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TSyntax"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Compat"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value),LEAN_SCALAR_PTR_LITERAL(233, 134, 124, 217, 96, 118, 79, 86)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70 = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 141, 19, 219, 57, 63, 124, 163)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(54, 195, 48, 34, 119, 0, 161, 186)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(95, 238, 135, 22, 62, 57, 216, 235)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(193, 79, 119, 168, 243, 41, 160, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(87, 78, 239, 73, 65, 82, 155, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(234, 37, 17, 192, 254, 35, 185, 251)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 230, 17, 18, 16, 137, 34, 13)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 122, 229, 163, 241, 81, 47, 255)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 49, 66, 28, 93, 238, 35, 16)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value),LEAN_SCALAR_PTR_LITERAL(13, 99, 135, 253, 30, 131, 204, 96)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value),LEAN_SCALAR_PTR_LITERAL(195, 203, 159, 105, 27, 114, 67, 184)}};
static const lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 88, 198, 182, 153, 159, 57)}};
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
lean_dec_ref(v___x_20_);
if (lean_obj_tag(v_val_22_) == 1)
{
uint8_t v_v_23_; 
v_v_23_ = lean_ctor_get_uint8(v_val_22_, 0);
lean_dec_ref(v_val_22_);
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
lean_object* v_options_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_options_71_ = lean_ctor_get(v___y_69_, 2);
v___x_72_ = l_Lean_Elab_pp_macroStack;
v___x_73_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v_options_71_, v___x_72_);
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
lean_object* v___x_105_; lean_object* v_env_106_; lean_object* v___x_107_; lean_object* v_mctx_108_; lean_object* v_lctx_109_; lean_object* v_options_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = lean_st_ref_get(v___y_101_);
v_mctx_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_mctx_108_);
lean_dec(v___x_107_);
v_lctx_109_ = lean_ctor_get(v___y_100_, 2);
v_options_110_ = lean_ctor_get(v___y_102_, 2);
lean_inc_ref(v_options_110_);
lean_inc_ref(v_lctx_109_);
v___x_111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_111_, 0, v_env_106_);
lean_ctor_set(v___x_111_, 1, v_mctx_108_);
lean_ctor_set(v___x_111_, 2, v_lctx_109_);
lean_ctor_set(v___x_111_, 3, v_options_110_);
v___x_112_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_msgData_99_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2___boxed(lean_object* v_msgData_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msgData_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v_macroStack_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_143_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 5);
v___x_130_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_121_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v___x_130_);
v_macroStack_132_ = lean_ctor_get(v___y_122_, 1);
v___x_133_ = l_Lean_Elab_getBetterRef(v_ref_129_, v_macroStack_132_);
lean_inc(v_macroStack_132_);
v___x_134_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_a_131_, v_macroStack_132_, v___y_126_);
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_143_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_133_);
lean_ctor_set(v___x_139_, 1, v_a_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
lean_ctor_set(v___x_137_, 0, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg___boxed(lean_object* v_msg_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0));
v___x_155_ = l_Lean_stringToMessageData(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2));
v___x_158_ = l_Lean_stringToMessageData(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(lean_object* v_constName_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_env_168_; lean_object* v___x_169_; 
v___x_167_ = lean_st_ref_get(v___y_165_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_env_168_);
lean_dec(v___x_167_);
lean_inc(v_constName_159_);
v___x_169_ = l_Lean_isInductiveCore_x3f(v_env_168_, v_constName_159_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_170_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1);
v___x_171_ = 0;
v___x_172_ = l_Lean_MessageData_ofConstName(v_constName_159_, v___x_171_);
v___x_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3);
v___x_175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_175_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_constName_159_);
v_val_177_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_169_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_val_177_);
lean_dec(v___x_169_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 0);
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_val_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___boxed(lean_object* v_constName_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_constName_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_193_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_194_; double v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_float_of_nat(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(lean_object* v_cls_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_ref_206_; lean_object* v___x_207_; lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_252_; 
v_ref_206_ = lean_ctor_get(v___y_203_, 5);
v___x_207_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_252_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_252_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_252_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v_traceState_213_; lean_object* v_env_214_; lean_object* v_nextMacroScope_215_; lean_object* v_ngen_216_; lean_object* v_auxDeclNGen_217_; lean_object* v_cache_218_; lean_object* v_messages_219_; lean_object* v_infoState_220_; lean_object* v_snapshotTasks_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_251_; 
v___x_212_ = lean_st_ref_take(v___y_204_);
v_traceState_213_ = lean_ctor_get(v___x_212_, 4);
v_env_214_ = lean_ctor_get(v___x_212_, 0);
v_nextMacroScope_215_ = lean_ctor_get(v___x_212_, 1);
v_ngen_216_ = lean_ctor_get(v___x_212_, 2);
v_auxDeclNGen_217_ = lean_ctor_get(v___x_212_, 3);
v_cache_218_ = lean_ctor_get(v___x_212_, 5);
v_messages_219_ = lean_ctor_get(v___x_212_, 6);
v_infoState_220_ = lean_ctor_get(v___x_212_, 7);
v_snapshotTasks_221_ = lean_ctor_get(v___x_212_, 8);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_251_ == 0)
{
v___x_223_ = v___x_212_;
v_isShared_224_ = v_isSharedCheck_251_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snapshotTasks_221_);
lean_inc(v_infoState_220_);
lean_inc(v_messages_219_);
lean_inc(v_cache_218_);
lean_inc(v_traceState_213_);
lean_inc(v_auxDeclNGen_217_);
lean_inc(v_ngen_216_);
lean_inc(v_nextMacroScope_215_);
lean_inc(v_env_214_);
lean_dec(v___x_212_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_251_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint64_t v_tid_225_; lean_object* v_traces_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_250_; 
v_tid_225_ = lean_ctor_get_uint64(v_traceState_213_, sizeof(void*)*1);
v_traces_226_ = lean_ctor_get(v_traceState_213_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_traceState_213_);
if (v_isSharedCheck_250_ == 0)
{
v___x_228_ = v_traceState_213_;
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_traces_226_);
lean_dec(v_traceState_213_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; double v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0);
v___x_232_ = 0;
v___x_233_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_234_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_234_, 0, v_cls_199_);
lean_ctor_set(v___x_234_, 1, v___x_230_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
lean_ctor_set_float(v___x_234_, sizeof(void*)*3, v___x_231_);
lean_ctor_set_float(v___x_234_, sizeof(void*)*3 + 8, v___x_231_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*3 + 16, v___x_232_);
v___x_235_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2));
v___x_236_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v_a_208_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_inc(v_ref_206_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_ref_206_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_PersistentArray_push___redArg(v_traces_226_, v___x_237_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_238_);
v___x_240_ = v___x_228_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_238_);
lean_ctor_set_uint64(v_reuseFailAlloc_249_, sizeof(void*)*1, v_tid_225_);
v___x_240_ = v_reuseFailAlloc_249_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___x_240_);
v___x_242_ = v___x_223_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_env_214_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_nextMacroScope_215_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_ngen_216_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_auxDeclNGen_217_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_cache_218_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_messages_219_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_infoState_220_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_snapshotTasks_221_);
v___x_242_ = v_reuseFailAlloc_248_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_243_ = lean_st_ref_set(v___y_204_, v___x_242_);
v___x_244_ = lean_box(0);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_244_);
v___x_246_ = v___x_210_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_253_, v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3));
v___x_277_ = l_Lean_mkCIdent(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Array_mkArray0(lean_box(0));
return v___x_294_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30));
v___x_329_ = l_String_toRawSubstring_x27(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_357_ = l_String_toRawSubstring_x27(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_449_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82));
v___x_450_ = l_Lean_Name_append(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(lean_object* v_declName_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_declName_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v_all_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_468_);
v_all_646_ = lean_ctor_get(v_a_469_, 3);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = l_List_lengthTR___redArg(v_all_646_);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
lean_dec(v___x_648_);
if (v___x_649_ == 0)
{
v___y_629_ = v_a_461_;
v___y_630_ = v_a_462_;
v___y_631_ = v_a_463_;
v___y_632_ = v_a_464_;
v___y_633_ = v_a_465_;
v___y_634_ = v_a_466_;
goto v___jp_628_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_469_);
v___x_650_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89);
v___x_651_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_650_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
v___jp_470_:
{
lean_object* v___x_477_; 
lean_inc(v_a_469_);
v___x_477_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_469_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_n(v_a_478_, 2);
lean_dec_ref(v___x_477_);
v___x_479_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_478_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1));
lean_inc(v_a_478_);
lean_inc(v_a_469_);
v___x_482_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_481_, v_a_469_, v_a_478_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
v___x_484_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3));
lean_inc(v_a_478_);
lean_inc(v_a_469_);
v___x_485_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_484_, v_a_469_, v_a_478_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref(v___x_485_);
v___x_487_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_469_, v_a_478_, v___y_475_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_603_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_603_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_603_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_603_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_options_492_; lean_object* v_ref_493_; lean_object* v_quotContext_494_; lean_object* v_currMacroScope_495_; lean_object* v_inheritedTraceOptions_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v_hasTrace_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_options_492_ = lean_ctor_get(v___y_475_, 2);
v_ref_493_ = lean_ctor_get(v___y_475_, 5);
v_quotContext_494_ = lean_ctor_get(v___y_475_, 10);
v_currMacroScope_495_ = lean_ctor_get(v___y_475_, 11);
v_inheritedTraceOptions_496_ = lean_ctor_get(v___y_475_, 13);
v___x_497_ = l_Array_append___redArg(v_a_480_, v_a_483_);
lean_dec(v_a_483_);
v___x_498_ = l_Array_append___redArg(v___x_497_, v_a_486_);
lean_dec(v_a_486_);
v___x_499_ = 0;
v___x_500_ = l_Lean_SourceInfo_fromRef(v_ref_493_, v___x_499_);
v___x_501_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8));
v___x_502_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9);
v___x_503_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11));
lean_inc_n(v___x_500_, 30);
v___x_504_ = l_Lean_Syntax_node1(v___x_500_, v___x_503_, v_a_488_);
v___x_505_ = l_Lean_Syntax_node2(v___x_500_, v___x_501_, v___x_502_, v___x_504_);
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14));
v___x_507_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16));
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17);
v___x_509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_509_, 0, v___x_500_);
lean_ctor_set(v___x_509_, 1, v___x_503_);
lean_ctor_set(v___x_509_, 2, v___x_508_);
lean_inc_ref_n(v___x_509_, 12);
v___x_510_ = l_Lean_Syntax_node7(v___x_500_, v___x_507_, v___x_509_, v___x_509_, v___x_509_, v___x_509_, v___x_509_, v___x_509_, v___x_509_);
v___x_511_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18));
v___x_512_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19));
v___x_513_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21));
v___x_514_ = l_Lean_Syntax_node1(v___x_500_, v___x_513_, v___x_509_);
v___x_515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_500_);
lean_ctor_set(v___x_515_, 1, v___x_511_);
v___x_516_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23));
v___x_517_ = l_Array_append___redArg(v___x_508_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v___x_500_);
lean_ctor_set(v___x_518_, 1, v___x_503_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25));
v___x_520_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26));
v___x_521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_500_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_Syntax_node2(v___x_500_, v___x_519_, v___x_521_, v___x_505_);
v___x_523_ = l_Lean_Syntax_node2(v___x_500_, v___x_516_, v___x_518_, v___x_522_);
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28));
v___x_525_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_500_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31);
v___x_528_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33));
lean_inc_n(v_currMacroScope_495_, 2);
lean_inc_n(v_quotContext_494_, 2);
v___x_529_ = l_Lean_addMacroScope(v_quotContext_494_, v___x_528_, v_currMacroScope_495_);
v___x_530_ = lean_box(0);
v___x_531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35));
v___x_532_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_532_, 0, v___x_500_);
lean_ctor_set(v___x_532_, 1, v___x_527_);
lean_ctor_set(v___x_532_, 2, v___x_529_);
lean_ctor_set(v___x_532_, 3, v___x_531_);
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37));
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39));
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40));
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_500_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42));
v___x_538_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43);
v___x_539_ = lean_box(0);
v___x_540_ = l_Lean_addMacroScope(v_quotContext_494_, v___x_539_, v_currMacroScope_495_);
v___x_541_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64));
v___x_542_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_542_, 0, v___x_500_);
lean_ctor_set(v___x_542_, 1, v___x_538_);
lean_ctor_set(v___x_542_, 2, v___x_540_);
lean_ctor_set(v___x_542_, 3, v___x_541_);
v___x_543_ = l_Lean_Syntax_node1(v___x_500_, v___x_537_, v___x_542_);
v___x_544_ = l_Lean_Syntax_node2(v___x_500_, v___x_534_, v___x_536_, v___x_543_);
v___x_545_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66));
v___x_546_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67));
v___x_547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_500_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69));
v___x_549_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71));
v___x_550_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73));
v___x_551_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74));
v___x_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_500_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_Syntax_node1(v___x_500_, v___x_550_, v___x_552_);
v___x_554_ = l_Lean_Syntax_node1(v___x_500_, v___x_503_, v___x_553_);
v___x_555_ = l_Lean_Syntax_node1(v___x_500_, v___x_549_, v___x_554_);
v___x_556_ = l_Lean_Syntax_node1(v___x_500_, v___x_548_, v___x_555_);
v___x_557_ = l_Lean_Syntax_node2(v___x_500_, v___x_545_, v___x_547_, v___x_556_);
v___x_558_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75));
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_500_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Syntax_node3(v___x_500_, v___x_533_, v___x_544_, v___x_557_, v___x_559_);
v___x_561_ = l_Lean_Syntax_node1(v___x_500_, v___x_503_, v___x_560_);
v___x_562_ = l_Lean_Syntax_node2(v___x_500_, v___x_501_, v___x_532_, v___x_561_);
v___x_563_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78));
v___x_564_ = l_Lean_Syntax_node2(v___x_500_, v___x_563_, v___x_509_, v___x_509_);
v___x_565_ = l_Lean_Syntax_node4(v___x_500_, v___x_524_, v___x_526_, v___x_562_, v___x_564_, v___x_509_);
v___x_566_ = l_Lean_Syntax_node6(v___x_500_, v___x_512_, v___x_514_, v___x_515_, v___x_509_, v___x_509_, v___x_523_, v___x_565_);
v_hasTrace_567_ = lean_ctor_get_uint8(v_options_492_, sizeof(void*)*1);
v___x_568_ = l_Lean_Syntax_node2(v___x_500_, v___x_506_, v___x_510_, v___x_566_);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_mk_empty_array_with_capacity(v___x_569_);
v___x_571_ = lean_array_push(v___x_570_, v___x_568_);
if (v_hasTrace_567_ == 0)
{
lean_object* v___x_573_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_571_);
v___x_573_ = v___x_490_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_576_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83);
v___x_577_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_496_, v_options_492_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_579_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_571_);
v___x_579_ = v___x_490_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_571_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_del_object(v___x_490_);
v___x_581_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85);
lean_inc_ref(v___x_571_);
v___x_582_ = lean_array_to_list(v___x_571_);
v___x_583_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(v___x_582_, v___x_530_);
v___x_584_ = l_Lean_MessageData_ofList(v___x_583_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_581_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v___x_575_, v___x_585_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_594_);
v___x_588_ = v___x_586_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_dec(v___x_586_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_571_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_571_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v___x_571_);
v_a_595_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_586_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_586_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_a_486_);
lean_dec(v_a_483_);
lean_dec(v_a_480_);
v_a_604_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_487_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_487_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_dec(v_a_483_);
lean_dec(v_a_480_);
lean_dec(v_a_478_);
lean_dec(v_a_469_);
return v___x_485_;
}
}
else
{
lean_dec(v_a_480_);
lean_dec(v_a_478_);
lean_dec(v_a_469_);
return v___x_482_;
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_478_);
lean_dec(v_a_469_);
v_a_612_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_479_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_479_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_a_469_);
v_a_620_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_477_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_477_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
v___jp_628_:
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_InductiveVal_isNested(v_a_469_);
if (v___x_635_ == 0)
{
v___y_471_ = v___y_629_;
v___y_472_ = v___y_630_;
v___y_473_ = v___y_631_;
v___y_474_ = v___y_632_;
v___y_475_ = v___y_633_;
v___y_476_ = v___y_634_;
goto v___jp_470_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_a_469_);
v___x_636_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87_once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87);
v___x_637_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_636_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_a_660_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_468_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_468_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed(lean_object* v_declName_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(v_declName_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(lean_object* v_cls_677_, lean_object* v_msg_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_677_, v_msg_678_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___boxed(lean_object* v_cls_687_, lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(v_cls_687_, v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(lean_object* v_00_u03b1_697_, lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___boxed(lean_object* v_00_u03b1_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(v_00_u03b1_707_, v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(lean_object* v_msgData_717_, lean_object* v_macroStack_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_717_, v_macroStack_718_, v___y_723_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___boxed(lean_object* v_msgData_727_, lean_object* v_macroStack_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(v_msgData_727_, v_macroStack_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(lean_object* v_as_737_, size_t v_i_738_, size_t v_stop_739_, lean_object* v_b_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_eq(v_i_738_, v_stop_739_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_array_uget_borrowed(v_as_737_, v_i_738_);
lean_inc(v___x_745_);
v___x_746_ = l_Lean_Elab_Command_elabCommand(v___x_745_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; size_t v___x_748_; size_t v___x_749_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
v___x_748_ = ((size_t)1ULL);
v___x_749_ = lean_usize_add(v_i_738_, v___x_748_);
v_i_738_ = v___x_749_;
v_b_740_ = v_a_747_;
goto _start;
}
else
{
return v___x_746_;
}
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_b_740_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0___boxed(lean_object* v_as_752_, lean_object* v_i_753_, lean_object* v_stop_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
size_t v_i_boxed_759_; size_t v_stop_boxed_760_; lean_object* v_res_761_; 
v_i_boxed_759_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_stop_boxed_760_ = lean_unbox_usize(v_stop_754_);
lean_dec(v_stop_754_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_as_752_, v_i_boxed_759_, v_stop_boxed_760_, v_b_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec_ref(v_as_752_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(lean_object* v___x_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_788_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_788_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_array_get_size(v_a_767_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
if (v___x_774_ == 0)
{
lean_object* v___x_776_; 
lean_dec(v_a_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_773_);
v___x_776_ = v___x_769_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_773_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
uint8_t v___x_778_; 
v___x_778_ = lean_nat_dec_le(v___x_772_, v___x_772_);
if (v___x_778_ == 0)
{
if (v___x_774_ == 0)
{
lean_object* v___x_780_; 
lean_dec(v_a_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_773_);
v___x_780_ = v___x_769_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_773_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
lean_del_object(v___x_769_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_of_nat(v___x_772_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_767_, v___x_782_, v___x_783_, v___x_773_, v___y_763_, v___y_764_);
lean_dec(v_a_767_);
return v___x_784_;
}
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
lean_del_object(v___x_769_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_772_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_767_, v___x_785_, v___x_786_, v___x_773_, v___y_763_, v___y_764_);
lean_dec(v_a_767_);
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_766_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_766_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed(lean_object* v___x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(v___x_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(lean_object* v_declName_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; 
lean_inc(v_declName_802_);
v___x_806_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_806_, 0, v_declName_802_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(v___f_807_, 0, v___x_806_);
v___x_808_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_802_, v___f_807_, v_a_803_, v_a_804_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___boxed(lean_object* v_declName_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_declName_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_env_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_817_ = lean_st_ref_get(v___y_815_);
v_env_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref(v_env_818_);
lean_dec(v___x_817_);
v___x_819_ = l_Lean_isInductiveCore(v_env_818_, v_declName_814_);
v___x_820_ = lean_box(v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_822_, v___y_823_);
lean_dec(v___y_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(lean_object* v_declName_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_826_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(v_declName_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(uint8_t v_____do__lift_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
if (v_____do__lift_836_ == 0)
{
uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = 1;
v___x_841_ = lean_box(v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
else
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = 0;
v___x_844_ = lean_box(v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v_____do__lift_1736__boxed_850_; lean_object* v_res_851_; 
v_____do__lift_1736__boxed_850_ = lean_unbox(v_____do__lift_846_);
v_res_851_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v_____do__lift_1736__boxed_850_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(lean_object* v_as_852_, size_t v_i_853_, size_t v_stop_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = lean_usize_dec_eq(v_i_853_, v_stop_854_);
if (v___x_858_ == 0)
{
uint8_t v___x_859_; uint8_t v_a_861_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_859_ = 1;
v___x_867_ = lean_array_uget_borrowed(v_as_852_, v_i_853_);
lean_inc(v___x_867_);
v___x_868_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v___x_867_, v___y_856_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_878_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_878_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_box(v___x_859_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_del_object(v___x_871_);
v_a_861_ = v___x_858_;
goto v___jp_860_;
}
}
}
else
{
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v___x_868_);
v___x_880_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
v_a_861_ = v___x_880_;
goto v___jp_860_;
}
else
{
return v___x_868_;
}
}
v___jp_860_:
{
if (v_a_861_ == 0)
{
size_t v___x_862_; size_t v___x_863_; 
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_853_, v___x_862_);
v_i_853_ = v___x_863_;
goto _start;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_box(v___x_859_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
else
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = 0;
v___x_882_ = lean_box(v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2___boxed(lean_object* v_as_884_, lean_object* v_i_885_, lean_object* v_stop_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
size_t v_i_boxed_890_; size_t v_stop_boxed_891_; lean_object* v_res_892_; 
v_i_boxed_890_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_stop_boxed_891_ = lean_unbox_usize(v_stop_886_);
lean_dec(v_stop_886_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_as_884_, v_i_boxed_890_, v_stop_boxed_891_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec_ref(v_as_884_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(lean_object* v_as_893_, size_t v_sz_894_, size_t v_i_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_lt(v_i_895_, v_sz_894_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_896_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_array_uget_borrowed(v_as_893_, v_i_895_);
lean_inc(v_a_902_);
v___x_903_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_a_902_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; size_t v___x_905_; size_t v___x_906_; 
lean_dec_ref(v___x_903_);
v___x_904_ = lean_box(0);
v___x_905_ = ((size_t)1ULL);
v___x_906_ = lean_usize_add(v_i_895_, v___x_905_);
v_i_895_ = v___x_906_;
v_b_896_ = v___x_904_;
goto _start;
}
else
{
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0___boxed(lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
size_t v_sz_boxed_915_; size_t v_i_boxed_916_; lean_object* v_res_917_; 
v_sz_boxed_915_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_916_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_as_908_, v_sz_boxed_915_, v_i_boxed_916_, v_b_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_as_908_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(lean_object* v_declNames_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___y_946_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_array_get_size(v_declNames_918_);
v___x_951_ = lean_nat_dec_lt(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
v___x_952_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_951_, v_a_919_, v_a_920_);
v___y_946_ = v___x_952_;
goto v___jp_945_;
}
else
{
if (v___x_951_ == 0)
{
goto v___jp_922_;
}
else
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_950_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_declNames_918_, v___x_953_, v___x_954_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref(v___x_955_);
v___x_957_ = lean_unbox(v_a_956_);
lean_dec(v_a_956_);
v___x_958_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_957_, v_a_919_, v_a_920_);
v___y_946_ = v___x_958_;
goto v___jp_945_;
}
else
{
v___y_946_ = v___x_955_;
goto v___jp_945_;
}
}
}
v___jp_922_:
{
lean_object* v___x_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v_sz_924_ = lean_array_size(v_declNames_918_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_declNames_918_, v_sz_924_, v___x_925_, v___x_923_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_935_; 
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_936_);
v___x_928_ = v___x_926_;
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_926_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = 1;
v___x_931_ = lean_box(v___x_930_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_931_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_926_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_926_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
v___jp_945_:
{
if (lean_obj_tag(v___y_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; 
v_a_947_ = lean_ctor_get(v___y_946_, 0);
v___x_948_ = lean_unbox(v_a_947_);
if (v___x_948_ == 0)
{
return v___y_946_;
}
else
{
lean_dec_ref(v___y_946_);
goto v___jp_922_;
}
}
else
{
return v___y_946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed(lean_object* v_declNames_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(v_declNames_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec_ref(v_declNames_959_);
return v_res_963_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_unsigned_to_nat(3244286355u);
v___x_1017_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1018_ = l_Lean_Name_num___override(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1021_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1022_ = l_Lean_Name_str___override(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1025_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1026_ = l_Lean_Name_str___override(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_unsigned_to_nat(2u);
v___x_1028_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1029_ = l_Lean_Name_num___override(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3));
v___x_1032_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_));
v___x_1033_ = l_Lean_Elab_registerDerivingHandler(v___x_1031_, v___x_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref(v___x_1033_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80));
v___x_1035_ = 0;
v___x_1036_ = lean_obj_once(&l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
v___x_1037_ = l_Lean_registerTraceClass(v___x_1034_, v___x_1035_, v___x_1036_);
return v___x_1037_;
}
else
{
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2____boxed(lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
return v_res_1039_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_LawfulBEq(uint8_t builtin) {
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
