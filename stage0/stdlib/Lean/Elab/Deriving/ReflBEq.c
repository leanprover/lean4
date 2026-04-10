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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_23_; double v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_float_of_nat(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(lean_object* v_cls_28_, lean_object* v_msg_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_ref_35_; lean_object* v___x_36_; lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_81_; 
v_ref_35_ = lean_ctor_get(v___y_32_, 5);
v___x_36_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msg_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_81_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_81_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_81_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v_traceState_42_; lean_object* v_env_43_; lean_object* v_nextMacroScope_44_; lean_object* v_ngen_45_; lean_object* v_auxDeclNGen_46_; lean_object* v_cache_47_; lean_object* v_messages_48_; lean_object* v_infoState_49_; lean_object* v_snapshotTasks_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_80_; 
v___x_41_ = lean_st_ref_take(v___y_33_);
v_traceState_42_ = lean_ctor_get(v___x_41_, 4);
v_env_43_ = lean_ctor_get(v___x_41_, 0);
v_nextMacroScope_44_ = lean_ctor_get(v___x_41_, 1);
v_ngen_45_ = lean_ctor_get(v___x_41_, 2);
v_auxDeclNGen_46_ = lean_ctor_get(v___x_41_, 3);
v_cache_47_ = lean_ctor_get(v___x_41_, 5);
v_messages_48_ = lean_ctor_get(v___x_41_, 6);
v_infoState_49_ = lean_ctor_get(v___x_41_, 7);
v_snapshotTasks_50_ = lean_ctor_get(v___x_41_, 8);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_80_ == 0)
{
v___x_52_ = v___x_41_;
v_isShared_53_ = v_isSharedCheck_80_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_snapshotTasks_50_);
lean_inc(v_infoState_49_);
lean_inc(v_messages_48_);
lean_inc(v_cache_47_);
lean_inc(v_traceState_42_);
lean_inc(v_auxDeclNGen_46_);
lean_inc(v_ngen_45_);
lean_inc(v_nextMacroScope_44_);
lean_inc(v_env_43_);
lean_dec(v___x_41_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_80_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
uint64_t v_tid_54_; lean_object* v_traces_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_79_; 
v_tid_54_ = lean_ctor_get_uint64(v_traceState_42_, sizeof(void*)*1);
v_traces_55_ = lean_ctor_get(v_traceState_42_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_traceState_42_);
if (v_isSharedCheck_79_ == 0)
{
v___x_57_ = v_traceState_42_;
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_traces_55_);
lean_dec(v_traceState_42_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; double v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0);
v___x_61_ = 0;
v___x_62_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1));
v___x_63_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_63_, 0, v_cls_28_);
lean_ctor_set(v___x_63_, 1, v___x_59_);
lean_ctor_set(v___x_63_, 2, v___x_62_);
lean_ctor_set_float(v___x_63_, sizeof(void*)*3, v___x_60_);
lean_ctor_set_float(v___x_63_, sizeof(void*)*3 + 8, v___x_60_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*3 + 16, v___x_61_);
v___x_64_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2));
v___x_65_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v_a_37_);
lean_ctor_set(v___x_65_, 2, v___x_64_);
lean_inc(v_ref_35_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_ref_35_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = l_Lean_PersistentArray_push___redArg(v_traces_55_, v___x_66_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_67_);
v___x_69_ = v___x_57_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_67_);
lean_ctor_set_uint64(v_reuseFailAlloc_78_, sizeof(void*)*1, v_tid_54_);
v___x_69_ = v_reuseFailAlloc_78_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_71_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 4, v___x_69_);
v___x_71_ = v___x_52_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_env_43_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_nextMacroScope_44_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v_ngen_45_);
lean_ctor_set(v_reuseFailAlloc_77_, 3, v_auxDeclNGen_46_);
lean_ctor_set(v_reuseFailAlloc_77_, 4, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_77_, 5, v_cache_47_);
lean_ctor_set(v_reuseFailAlloc_77_, 6, v_messages_48_);
lean_ctor_set(v_reuseFailAlloc_77_, 7, v_infoState_49_);
lean_ctor_set(v_reuseFailAlloc_77_, 8, v_snapshotTasks_50_);
v___x_71_ = v_reuseFailAlloc_77_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_72_ = lean_st_ref_set(v___y_33_, v___x_71_);
v___x_73_ = lean_box(0);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_73_);
v___x_75_ = v___x_39_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_82_, lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_82_, v_msg_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
if (lean_obj_tag(v_a_90_) == 0)
{
lean_object* v___x_92_; 
v___x_92_ = l_List_reverse___redArg(v_a_91_);
return v___x_92_;
}
else
{
lean_object* v_head_93_; lean_object* v_tail_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_103_; 
v_head_93_ = lean_ctor_get(v_a_90_, 0);
v_tail_94_ = lean_ctor_get(v_a_90_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_a_90_);
if (v_isSharedCheck_103_ == 0)
{
v___x_96_ = v_a_90_;
v_isShared_97_ = v_isSharedCheck_103_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_tail_94_);
lean_inc(v_head_93_);
lean_dec(v_a_90_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_103_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = l_Lean_MessageData_ofSyntax(v_head_93_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_a_91_);
lean_ctor_set(v___x_96_, 0, v___x_98_);
v___x_100_ = v___x_96_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_a_91_);
v___x_100_ = v_reuseFailAlloc_102_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
v_a_90_ = v_tail_94_;
v_a_91_ = v___x_100_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_box(1);
v___x_105_ = l_Lean_MessageData_ofFormat(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2));
v___x_110_ = l_Lean_MessageData_ofFormat(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
return v_x_111_;
}
else
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_136_; 
v_head_113_ = lean_ctor_get(v_x_112_, 0);
v_tail_114_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_136_ == 0)
{
v___x_116_ = v_x_112_;
v_isShared_117_ = v_isSharedCheck_136_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_tail_114_);
lean_inc(v_head_113_);
lean_dec(v_x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_136_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_before_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_134_; 
v_before_118_ = lean_ctor_get(v_head_113_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_head_113_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_head_113_, 1);
lean_dec(v_unused_135_);
v___x_120_ = v_head_113_;
v_isShared_121_ = v_isSharedCheck_134_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_before_118_);
lean_dec(v_head_113_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_134_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_121_ == 0)
{
lean_ctor_set_tag(v___x_120_, 7);
lean_ctor_set(v___x_120_, 1, v___x_122_);
lean_ctor_set(v___x_120_, 0, v_x_111_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_x_111_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_133_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 7);
lean_ctor_set(v___x_116_, 1, v___x_125_);
lean_ctor_set(v___x_116_, 0, v___x_124_);
v___x_127_ = v___x_116_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_132_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = l_Lean_MessageData_ofSyntax(v_before_118_);
v___x_129_ = l_Lean_indentD(v___x_128_);
v___x_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_127_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v_x_111_ = v___x_130_;
v_x_112_ = v_tail_114_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
lean_object* v_name_139_; lean_object* v_defValue_140_; lean_object* v_map_141_; lean_object* v___x_142_; 
v_name_139_ = lean_ctor_get(v_opt_138_, 0);
v_defValue_140_ = lean_ctor_get(v_opt_138_, 1);
v_map_141_ = lean_ctor_get(v_opts_137_, 0);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_141_, v_name_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = lean_unbox(v_defValue_140_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; 
v_val_144_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_144_);
lean_dec_ref(v___x_142_);
if (lean_obj_tag(v_val_144_) == 1)
{
uint8_t v_v_145_; 
v_v_145_ = lean_ctor_get_uint8(v_val_144_, 0);
lean_dec_ref(v_val_144_);
return v_v_145_;
}
else
{
uint8_t v___x_146_; 
lean_dec(v_val_144_);
v___x_146_ = lean_unbox(v_defValue_140_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_147_, v_opt_148_);
lean_dec_ref(v_opt_148_);
lean_dec_ref(v_opts_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1));
v___x_155_ = l_Lean_MessageData_ofFormat(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(lean_object* v_msgData_156_, lean_object* v_macroStack_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_options_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_options_160_ = lean_ctor_get(v___y_158_, 2);
v___x_161_ = l_Lean_Elab_pp_macroStack;
v___x_162_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v_options_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
lean_dec(v_macroStack_157_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v_msgData_156_);
return v___x_163_;
}
else
{
if (lean_obj_tag(v_macroStack_157_) == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v_msgData_156_);
return v___x_164_;
}
else
{
lean_object* v_head_165_; lean_object* v_after_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_181_; 
v_head_165_ = lean_ctor_get(v_macroStack_157_, 0);
lean_inc(v_head_165_);
v_after_166_ = lean_ctor_get(v_head_165_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_head_165_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_head_165_, 0);
lean_dec(v_unused_182_);
v___x_168_ = v_head_165_;
v_isShared_169_ = v_isSharedCheck_181_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_after_166_);
lean_dec(v_head_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_181_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 7);
lean_ctor_set(v___x_168_, 1, v___x_170_);
lean_ctor_set(v___x_168_, 0, v_msgData_156_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_msgData_156_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_180_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_msgData_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_173_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_MessageData_ofSyntax(v_after_166_);
v___x_176_ = l_Lean_indentD(v___x_175_);
v_msgData_177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_177_, 0, v___x_174_);
lean_ctor_set(v_msgData_177_, 1, v___x_176_);
v___x_178_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(v_msgData_177_, v_macroStack_157_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_183_, lean_object* v_macroStack_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_183_, v_macroStack_184_, v___y_185_);
lean_dec_ref(v___y_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_ref_196_; lean_object* v___x_197_; lean_object* v_a_198_; lean_object* v_macroStack_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_ref_196_ = lean_ctor_get(v___y_193_, 5);
v___x_197_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msg_188_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
v_macroStack_199_ = lean_ctor_get(v___y_189_, 1);
lean_inc_n(v_macroStack_199_, 2);
v___x_200_ = l_Lean_Elab_getBetterRef(v_ref_196_, v_macroStack_199_);
v___x_201_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_a_198_, v_macroStack_199_, v___y_193_);
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
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_200_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___boxed(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(lean_object* v_constName_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v_env_235_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_get(v___y_232_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_env_235_);
lean_dec(v___x_234_);
lean_inc(v_constName_226_);
v___x_236_ = l_Lean_isInductiveCore_x3f(v_env_235_, v_constName_226_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_237_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1);
v___x_238_ = 0;
v___x_239_ = l_Lean_MessageData_ofConstName(v_constName_226_, v___x_238_);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_237_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_242_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_constName_226_);
v_val_244_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_236_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v___x_236_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_val_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___boxed(lean_object* v_constName_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_constName_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_260_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3));
v___x_277_ = l_Lean_mkCIdent(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Array_mkArray0(lean_box(0));
return v___x_294_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36));
v___x_347_ = l_String_toRawSubstring_x27(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_400_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61));
v___x_401_ = l_Lean_Name_append(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63));
v___x_404_ = l_Lean_stringToMessageData(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(lean_object* v_declName_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_declName_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v_all_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref(v___x_419_);
v_all_590_ = lean_ctor_get(v_a_420_, 3);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = l_List_lengthTR___redArg(v_all_590_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
lean_dec(v___x_592_);
if (v___x_593_ == 0)
{
v___y_573_ = v_a_412_;
v___y_574_ = v_a_413_;
v___y_575_ = v_a_414_;
v___y_576_ = v_a_415_;
v___y_577_ = v_a_416_;
v___y_578_ = v_a_417_;
goto v___jp_572_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_a_420_);
v___x_594_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68);
v___x_595_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_594_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
v___jp_421_:
{
lean_object* v___x_428_; 
lean_inc(v_a_420_);
v___x_428_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_420_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_429_, 2);
lean_dec_ref(v___x_428_);
v___x_430_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_429_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___x_430_);
v___x_432_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1));
lean_inc(v_a_429_);
lean_inc(v_a_420_);
v___x_433_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_432_, v_a_420_, v_a_429_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref(v___x_433_);
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3));
lean_inc(v_a_429_);
lean_inc(v_a_420_);
v___x_436_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_435_, v_a_420_, v_a_429_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
v___x_438_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_420_, v_a_429_, v___y_426_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_547_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_547_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_547_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_547_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_options_443_; lean_object* v_ref_444_; lean_object* v_quotContext_445_; lean_object* v_currMacroScope_446_; lean_object* v_inheritedTraceOptions_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v_hasTrace_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_options_443_ = lean_ctor_get(v___y_426_, 2);
v_ref_444_ = lean_ctor_get(v___y_426_, 5);
v_quotContext_445_ = lean_ctor_get(v___y_426_, 10);
v_currMacroScope_446_ = lean_ctor_get(v___y_426_, 11);
v_inheritedTraceOptions_447_ = lean_ctor_get(v___y_426_, 13);
v___x_448_ = l_Array_append___redArg(v_a_431_, v_a_434_);
lean_dec(v_a_434_);
v___x_449_ = l_Array_append___redArg(v___x_448_, v_a_437_);
lean_dec(v_a_437_);
v___x_450_ = 0;
v___x_451_ = l_Lean_SourceInfo_fromRef(v_ref_444_, v___x_450_);
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8));
v___x_453_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9);
v___x_454_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11));
lean_inc_n(v___x_451_, 28);
v___x_455_ = l_Lean_Syntax_node1(v___x_451_, v___x_454_, v_a_439_);
v___x_456_ = l_Lean_Syntax_node2(v___x_451_, v___x_452_, v___x_453_, v___x_455_);
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14));
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16));
v___x_459_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17);
v___x_460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_460_, 0, v___x_451_);
lean_ctor_set(v___x_460_, 1, v___x_454_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
lean_inc_ref_n(v___x_460_, 14);
v___x_461_ = l_Lean_Syntax_node7(v___x_451_, v___x_458_, v___x_460_, v___x_460_, v___x_460_, v___x_460_, v___x_460_, v___x_460_, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18));
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19));
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21));
v___x_465_ = l_Lean_Syntax_node1(v___x_451_, v___x_464_, v___x_460_);
v___x_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_451_);
lean_ctor_set(v___x_466_, 1, v___x_462_);
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23));
v___x_468_ = l_Array_append___redArg(v___x_459_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_469_, 0, v___x_451_);
lean_ctor_set(v___x_469_, 1, v___x_454_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25));
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26));
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_451_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_Syntax_node2(v___x_451_, v___x_470_, v___x_472_, v___x_456_);
v___x_474_ = l_Lean_Syntax_node2(v___x_451_, v___x_467_, v___x_469_, v___x_473_);
v___x_475_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28));
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29));
v___x_477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_451_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31));
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33));
v___x_480_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35));
v___x_481_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37);
v___x_482_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38));
lean_inc(v_currMacroScope_446_);
lean_inc(v_quotContext_445_);
v___x_483_ = l_Lean_addMacroScope(v_quotContext_445_, v___x_482_, v_currMacroScope_446_);
v___x_484_ = lean_box(0);
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40));
v___x_486_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_486_, 0, v___x_451_);
lean_ctor_set(v___x_486_, 1, v___x_481_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
lean_ctor_set(v___x_486_, 3, v___x_485_);
v___x_487_ = l_Lean_Syntax_node2(v___x_451_, v___x_480_, v___x_486_, v___x_460_);
v___x_488_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42));
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43));
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_451_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45));
v___x_492_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46));
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_451_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49));
v___x_495_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51));
v___x_496_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54));
v___x_497_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55));
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_451_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_Syntax_node1(v___x_451_, v___x_496_, v___x_498_);
v___x_500_ = l_Lean_Syntax_node1(v___x_451_, v___x_454_, v___x_499_);
v___x_501_ = l_Lean_Syntax_node1(v___x_451_, v___x_495_, v___x_500_);
v___x_502_ = l_Lean_Syntax_node1(v___x_451_, v___x_494_, v___x_501_);
v___x_503_ = l_Lean_Syntax_node2(v___x_451_, v___x_491_, v___x_493_, v___x_502_);
v___x_504_ = l_Lean_Syntax_node3(v___x_451_, v___x_488_, v___x_490_, v___x_460_, v___x_503_);
v___x_505_ = l_Lean_Syntax_node3(v___x_451_, v___x_454_, v___x_460_, v___x_460_, v___x_504_);
v___x_506_ = l_Lean_Syntax_node2(v___x_451_, v___x_479_, v___x_487_, v___x_505_);
v___x_507_ = l_Lean_Syntax_node1(v___x_451_, v___x_454_, v___x_506_);
v___x_508_ = l_Lean_Syntax_node1(v___x_451_, v___x_478_, v___x_507_);
v___x_509_ = l_Lean_Syntax_node3(v___x_451_, v___x_475_, v___x_477_, v___x_508_, v___x_460_);
v___x_510_ = l_Lean_Syntax_node6(v___x_451_, v___x_463_, v___x_465_, v___x_466_, v___x_460_, v___x_460_, v___x_474_, v___x_509_);
v_hasTrace_511_ = lean_ctor_get_uint8(v_options_443_, sizeof(void*)*1);
v___x_512_ = l_Lean_Syntax_node2(v___x_451_, v___x_457_, v___x_461_, v___x_510_);
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_mk_empty_array_with_capacity(v___x_513_);
v___x_515_ = lean_array_push(v___x_514_, v___x_512_);
if (v_hasTrace_511_ == 0)
{
lean_object* v___x_517_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_515_);
v___x_517_ = v___x_441_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_520_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62);
v___x_521_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_447_, v_options_443_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_523_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_515_);
v___x_523_ = v___x_441_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_515_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_del_object(v___x_441_);
v___x_525_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64);
lean_inc_ref(v___x_515_);
v___x_526_ = lean_array_to_list(v___x_515_);
v___x_527_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(v___x_526_, v___x_484_);
v___x_528_ = l_Lean_MessageData_ofList(v___x_527_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_525_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v___x_519_, v___x_529_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v___x_530_, 0);
lean_dec(v_unused_538_);
v___x_532_ = v___x_530_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_dec(v___x_530_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_515_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_515_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v___x_515_);
v_a_539_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_530_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_a_437_);
lean_dec(v_a_434_);
lean_dec(v_a_431_);
v_a_548_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_438_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_438_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_dec(v_a_434_);
lean_dec(v_a_431_);
lean_dec(v_a_429_);
lean_dec(v_a_420_);
return v___x_436_;
}
}
else
{
lean_dec(v_a_431_);
lean_dec(v_a_429_);
lean_dec(v_a_420_);
return v___x_433_;
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_a_429_);
lean_dec(v_a_420_);
v_a_556_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_430_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_430_);
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
lean_dec(v_a_420_);
v_a_564_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_428_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_428_);
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
v___jp_572_:
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_InductiveVal_isNested(v_a_420_);
if (v___x_579_ == 0)
{
v___y_422_ = v___y_573_;
v___y_423_ = v___y_574_;
v___y_424_ = v___y_575_;
v___y_425_ = v___y_576_;
v___y_426_ = v___y_577_;
v___y_427_ = v___y_578_;
goto v___jp_421_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_420_);
v___x_580_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66, &l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66_once, _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66);
v___x_581_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_580_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_a_604_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_419_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_419_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed(lean_object* v_declName_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(v_declName_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(lean_object* v_cls_621_, lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_621_, v_msg_622_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___boxed(lean_object* v_cls_631_, lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(v_cls_631_, v_msg_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(lean_object* v_00_u03b1_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___boxed(lean_object* v_00_u03b1_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(v_00_u03b1_651_, v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(lean_object* v_msgData_661_, lean_object* v_macroStack_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_661_, v_macroStack_662_, v___y_667_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___boxed(lean_object* v_msgData_671_, lean_object* v_macroStack_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(v_msgData_671_, v_macroStack_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(lean_object* v_as_681_, size_t v_i_682_, size_t v_stop_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_eq(v_i_682_, v_stop_683_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_array_uget_borrowed(v_as_681_, v_i_682_);
lean_inc(v___x_689_);
v___x_690_ = l_Lean_Elab_Command_elabCommand(v___x_689_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; size_t v___x_692_; size_t v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_682_, v___x_692_);
v_i_682_ = v___x_693_;
v_b_684_ = v_a_691_;
goto _start;
}
else
{
return v___x_690_;
}
}
else
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_b_684_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0___boxed(lean_object* v_as_696_, lean_object* v_i_697_, lean_object* v_stop_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
size_t v_i_boxed_703_; size_t v_stop_boxed_704_; lean_object* v_res_705_; 
v_i_boxed_703_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_stop_boxed_704_ = lean_unbox_usize(v_stop_698_);
lean_dec(v_stop_698_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_as_696_, v_i_boxed_703_, v_stop_boxed_704_, v_b_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_as_696_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(lean_object* v___x_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_732_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_732_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_732_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_732_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_a_711_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
if (v___x_718_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_720_ = v___x_713_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_717_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_le(v___x_716_, v___x_716_);
if (v___x_722_ == 0)
{
if (v___x_718_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_724_ = v___x_713_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_717_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
else
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
lean_del_object(v___x_713_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = lean_usize_of_nat(v___x_716_);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_711_, v___x_726_, v___x_727_, v___x_717_, v___y_707_, v___y_708_);
lean_dec(v_a_711_);
return v___x_728_;
}
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
lean_del_object(v___x_713_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_716_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_711_, v___x_729_, v___x_730_, v___x_717_, v___y_707_, v___y_708_);
lean_dec(v_a_711_);
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_710_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_710_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed(lean_object* v___x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(v___x_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(lean_object* v_declName_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___f_751_; lean_object* v___x_752_; 
lean_inc(v_declName_746_);
v___x_750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_750_, 0, v_declName_746_);
v___f_751_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed), 4, 1);
lean_closure_set(v___f_751_, 0, v___x_750_);
v___x_752_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_746_, v___f_751_, v_a_747_, v_a_748_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___boxed(lean_object* v_declName_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_declName_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(lean_object* v_declName_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v_env_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_761_ = lean_st_ref_get(v___y_759_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_env_762_);
lean_dec(v___x_761_);
v___x_763_ = l_Lean_isInductiveCore(v_env_762_, v_declName_758_);
v___x_764_ = lean_box(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_766_, v___y_767_);
lean_dec(v___y_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(lean_object* v_declName_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_770_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___boxed(lean_object* v_declName_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(v_declName_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(uint8_t v_____do__lift_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
if (v_____do__lift_780_ == 0)
{
uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = 1;
v___x_785_ = lean_box(v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
else
{
uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = 0;
v___x_788_ = lean_box(v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_____do__lift_1736__boxed_794_; lean_object* v_res_795_; 
v_____do__lift_1736__boxed_794_ = lean_unbox(v_____do__lift_790_);
v_res_795_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v_____do__lift_1736__boxed_794_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(lean_object* v_as_796_, size_t v_i_797_, size_t v_stop_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = lean_usize_dec_eq(v_i_797_, v_stop_798_);
if (v___x_802_ == 0)
{
uint8_t v___x_803_; uint8_t v_a_805_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_803_ = 1;
v___x_811_ = lean_array_uget_borrowed(v_as_796_, v_i_797_);
lean_inc(v___x_811_);
v___x_812_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v___x_811_, v___y_800_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___x_817_; 
v___x_817_ = lean_unbox(v_a_813_);
lean_dec(v_a_813_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_box(v___x_803_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_del_object(v___x_815_);
v_a_805_ = v___x_802_;
goto v___jp_804_;
}
}
}
else
{
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_823_; uint8_t v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_812_);
v___x_824_ = lean_unbox(v_a_823_);
lean_dec(v_a_823_);
v_a_805_ = v___x_824_;
goto v___jp_804_;
}
else
{
return v___x_812_;
}
}
v___jp_804_:
{
if (v_a_805_ == 0)
{
size_t v___x_806_; size_t v___x_807_; 
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_797_, v___x_806_);
v_i_797_ = v___x_807_;
goto _start;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_box(v___x_803_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
else
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = 0;
v___x_826_ = lean_box(v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2___boxed(lean_object* v_as_828_, lean_object* v_i_829_, lean_object* v_stop_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
size_t v_i_boxed_834_; size_t v_stop_boxed_835_; lean_object* v_res_836_; 
v_i_boxed_834_ = lean_unbox_usize(v_i_829_);
lean_dec(v_i_829_);
v_stop_boxed_835_ = lean_unbox_usize(v_stop_830_);
lean_dec(v_stop_830_);
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_as_828_, v_i_boxed_834_, v_stop_boxed_835_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v_as_828_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(lean_object* v_as_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_b_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_b_840_);
return v___x_845_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_array_uget_borrowed(v_as_837_, v_i_839_);
lean_inc(v_a_846_);
v___x_847_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_a_846_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_848_; size_t v___x_849_; size_t v___x_850_; 
lean_dec_ref(v___x_847_);
v___x_848_ = lean_box(0);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_839_, v___x_849_);
v_i_839_ = v___x_850_;
v_b_840_ = v___x_848_;
goto _start;
}
else
{
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0___boxed(lean_object* v_as_852_, lean_object* v_sz_853_, lean_object* v_i_854_, lean_object* v_b_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
size_t v_sz_boxed_859_; size_t v_i_boxed_860_; lean_object* v_res_861_; 
v_sz_boxed_859_ = lean_unbox_usize(v_sz_853_);
lean_dec(v_sz_853_);
v_i_boxed_860_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_as_852_, v_sz_boxed_859_, v_i_boxed_860_, v_b_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v_as_852_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(lean_object* v_declNames_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___y_890_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_array_get_size(v_declNames_862_);
v___x_895_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_895_, v_a_863_, v_a_864_);
v___y_890_ = v___x_896_;
goto v___jp_889_;
}
else
{
if (v___x_895_ == 0)
{
goto v___jp_866_;
}
else
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((size_t)0ULL);
v___x_898_ = lean_usize_of_nat(v___x_894_);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_declNames_862_, v___x_897_, v___x_898_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; uint8_t v___x_901_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
v___x_901_ = lean_unbox(v_a_900_);
lean_dec(v_a_900_);
v___x_902_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_901_, v_a_863_, v_a_864_);
v___y_890_ = v___x_902_;
goto v___jp_889_;
}
else
{
v___y_890_ = v___x_899_;
goto v___jp_889_;
}
}
}
v___jp_866_:
{
lean_object* v___x_867_; size_t v_sz_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_867_ = lean_box(0);
v_sz_868_ = lean_array_size(v_declNames_862_);
v___x_869_ = ((size_t)0ULL);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_declNames_862_, v_sz_868_, v___x_869_, v___x_867_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_879_; 
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v___x_870_, 0);
lean_dec(v_unused_880_);
v___x_872_ = v___x_870_;
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
else
{
lean_dec(v___x_870_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = 1;
v___x_875_ = lean_box(v___x_874_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_870_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_870_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
v___jp_889_:
{
if (lean_obj_tag(v___y_890_) == 0)
{
lean_object* v_a_891_; uint8_t v___x_892_; 
v_a_891_ = lean_ctor_get(v___y_890_, 0);
v___x_892_ = lean_unbox(v_a_891_);
if (v___x_892_ == 0)
{
return v___y_890_;
}
else
{
lean_dec_ref(v___y_890_);
goto v___jp_866_;
}
}
else
{
return v___y_890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed(lean_object* v_declNames_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(v_declNames_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec_ref(v_declNames_903_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3));
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_));
v___x_977_ = l_Lean_Elab_registerDerivingHandler(v___x_975_, v___x_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec_ref(v___x_977_);
v___x_978_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59));
v___x_979_ = 0;
v___x_980_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_));
v___x_981_ = l_Lean_registerTraceClass(v___x_978_, v___x_979_, v___x_980_);
return v___x_981_;
}
else
{
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2____boxed(lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
return v_res_983_;
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
