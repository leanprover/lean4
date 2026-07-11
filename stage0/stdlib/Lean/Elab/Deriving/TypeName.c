// Lean compiler output
// Module: Lean.Elab.Deriving.TypeName
// Imports: public import Lean.Elab.Deriving.Basic
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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "classDefReducibility"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 250, 156, 61, 219, 107, 141, 135)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 199, 74, 147, 156, 95, 99, 180)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(79, 160, 60, 55, 136, 115, 80, 144)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instImpl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(232, 28, 47, 102, 93, 94, 89, 5)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TypeName"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(175, 11, 174, 247, 162, 85, 247, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__49_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__51_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 247, 82, 130, 198, 123, 173)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = " has universe level parameters"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(lean_object* v_o_4_, lean_object* v_k_5_, uint8_t v_v_6_){
_start:
{
lean_object* v_map_7_; uint8_t v_hasTrace_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_22_; 
v_map_7_ = lean_ctor_get(v_o_4_, 0);
v_hasTrace_8_ = lean_ctor_get_uint8(v_o_4_, sizeof(void*)*1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_o_4_);
if (v_isSharedCheck_22_ == 0)
{
v___x_10_ = v_o_4_;
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_map_7_);
lean_dec(v_o_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_12_, 0, v_v_6_);
lean_inc(v_k_5_);
v___x_13_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_5_, v___x_12_, v_map_7_);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_17_; 
v___x_14_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___closed__1));
v___x_15_ = l_Lean_Name_isPrefixOf(v___x_14_, v_k_5_);
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_13_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*1, v___x_15_);
return v___x_17_;
}
}
else
{
lean_object* v___x_20_; 
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_20_ = v___x_10_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_21_, sizeof(void*)*1, v_hasTrace_8_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0___boxed(lean_object* v_o_23_, lean_object* v_k_24_, lean_object* v_v_25_){
_start:
{
uint8_t v_v_boxed_26_; lean_object* v_res_27_; 
v_v_boxed_26_ = lean_unbox(v_v_25_);
v_res_27_ = l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(v_o_23_, v_k_24_, v_v_boxed_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(lean_object* v___y_28_){
_start:
{
lean_object* v___x_30_; lean_object* v_env_31_; lean_object* v___x_32_; lean_object* v_mainModule_33_; lean_object* v___x_34_; 
v___x_30_ = lean_st_ref_get(v___y_28_);
v_env_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc_ref(v_env_31_);
lean_dec(v___x_30_);
v___x_32_ = l_Lean_Environment_header(v_env_31_);
lean_dec_ref(v_env_31_);
v_mainModule_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_mainModule_33_);
lean_dec_ref(v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v_mainModule_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg___boxed(lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_35_);
lean_dec(v___y_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___boxed(lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1(v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0(lean_object* v_scope_51_){
_start:
{
lean_object* v_header_52_; lean_object* v_opts_53_; lean_object* v_currNamespace_54_; lean_object* v_openDecls_55_; lean_object* v_levelNames_56_; lean_object* v_varDecls_57_; lean_object* v_varUIds_58_; lean_object* v_includedVars_59_; lean_object* v_omittedVars_60_; uint8_t v_isNoncomputable_61_; uint8_t v_isPublic_62_; uint8_t v_isMeta_63_; lean_object* v_attrs_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_74_; 
v_header_52_ = lean_ctor_get(v_scope_51_, 0);
v_opts_53_ = lean_ctor_get(v_scope_51_, 1);
v_currNamespace_54_ = lean_ctor_get(v_scope_51_, 2);
v_openDecls_55_ = lean_ctor_get(v_scope_51_, 3);
v_levelNames_56_ = lean_ctor_get(v_scope_51_, 4);
v_varDecls_57_ = lean_ctor_get(v_scope_51_, 5);
v_varUIds_58_ = lean_ctor_get(v_scope_51_, 6);
v_includedVars_59_ = lean_ctor_get(v_scope_51_, 7);
v_omittedVars_60_ = lean_ctor_get(v_scope_51_, 8);
v_isNoncomputable_61_ = lean_ctor_get_uint8(v_scope_51_, sizeof(void*)*10);
v_isPublic_62_ = lean_ctor_get_uint8(v_scope_51_, sizeof(void*)*10 + 1);
v_isMeta_63_ = lean_ctor_get_uint8(v_scope_51_, sizeof(void*)*10 + 2);
v_attrs_64_ = lean_ctor_get(v_scope_51_, 9);
v_isSharedCheck_74_ = !lean_is_exclusive(v_scope_51_);
if (v_isSharedCheck_74_ == 0)
{
v___x_66_ = v_scope_51_;
v_isShared_67_ = v_isSharedCheck_74_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_attrs_64_);
lean_inc(v_omittedVars_60_);
lean_inc(v_includedVars_59_);
lean_inc(v_varUIds_58_);
lean_inc(v_varDecls_57_);
lean_inc(v_levelNames_56_);
lean_inc(v_openDecls_55_);
lean_inc(v_currNamespace_54_);
lean_inc(v_opts_53_);
lean_inc(v_header_52_);
lean_dec(v_scope_51_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_74_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_68_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__0___closed__2));
v___x_69_ = 0;
v___x_70_ = l_Lean_Options_set___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__0(v_opts_53_, v___x_68_, v___x_69_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_70_);
v___x_72_ = v___x_66_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_header_52_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v_currNamespace_54_);
lean_ctor_set(v_reuseFailAlloc_73_, 3, v_openDecls_55_);
lean_ctor_set(v_reuseFailAlloc_73_, 4, v_levelNames_56_);
lean_ctor_set(v_reuseFailAlloc_73_, 5, v_varDecls_57_);
lean_ctor_set(v_reuseFailAlloc_73_, 6, v_varUIds_58_);
lean_ctor_set(v_reuseFailAlloc_73_, 7, v_includedVars_59_);
lean_ctor_set(v_reuseFailAlloc_73_, 8, v_omittedVars_60_);
lean_ctor_set(v_reuseFailAlloc_73_, 9, v_attrs_64_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*10, v_isNoncomputable_61_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*10 + 1, v_isPublic_62_);
lean_ctor_set_uint8(v_reuseFailAlloc_73_, sizeof(void*)*10 + 2, v_isMeta_63_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2(lean_object* v___f_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___f_75_, v___y_76_, v___y_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref_known(v___x_79_, 1);
v___x_81_ = l_Lean_Elab_Command_elabCommand(v_a_80_, v___y_76_, v___y_77_);
return v___x_81_;
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_a_82_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_79_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2___boxed(lean_object* v___f_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2(v___f_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_94_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__8));
v___x_105_ = l_String_toRawSubstring_x27(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__13));
v___x_112_ = l_String_toRawSubstring_x27(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Array_mkArray0(lean_box(0));
return v___x_135_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__35));
v___x_157_ = l_String_toRawSubstring_x27(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__46));
v___x_182_ = l_String_toRawSubstring_x27(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__62));
v___x_219_ = l_String_toRawSubstring_x27(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1(lean_object* v_a_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Elab_Command_getRef___redArg(v___y_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_237_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_419_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_419_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_419_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_419_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_quotContext_x3f_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v_a_334_; 
v_quotContext_x3f_247_ = lean_ctor_get(v___y_237_, 5);
lean_inc(v_quotContext_x3f_247_);
lean_dec_ref(v___y_237_);
v___x_248_ = 0;
v___x_249_ = l_Lean_SourceInfo_fromRef(v_a_241_, v___x_248_);
lean_dec(v_a_241_);
if (lean_obj_tag(v_quotContext_x3f_247_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_238_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_a_334_ = v_a_409_;
goto v___jp_333_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v___x_249_);
lean_del_object(v___x_245_);
lean_dec(v_a_243_);
lean_dec(v_a_236_);
v_a_410_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_408_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_408_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_val_418_; 
v_val_418_ = lean_ctor_get(v_quotContext_x3f_247_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_quotContext_x3f_247_, 1);
v_a_334_ = v_val_418_;
goto v___jp_333_;
}
v___jp_250_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_inc_n(v___y_267_, 4);
lean_inc_n(v___x_249_, 28);
v___x_275_ = l_Lean_Syntax_node2(v___x_249_, v___y_267_, v___y_251_, v___y_274_);
v___x_276_ = l_Lean_Syntax_node2(v___x_249_, v___y_261_, v___y_263_, v___x_275_);
v___x_277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0));
v___x_278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1));
lean_inc_ref_n(v___y_270_, 8);
lean_inc_ref_n(v___y_252_, 8);
v___x_279_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___x_277_, v___x_278_);
lean_inc_n(v___y_273_, 23);
v___x_280_ = l_Lean_Syntax_node2(v___x_249_, v___x_279_, v___y_273_, v___y_273_);
lean_inc(v___x_280_);
lean_inc(v___y_264_);
lean_inc_n(v___y_258_, 2);
v___x_281_ = l_Lean_Syntax_node4(v___x_249_, v___y_258_, v___y_264_, v___x_276_, v___x_280_, v___y_273_);
lean_inc(v___y_265_);
v___x_282_ = l_Lean_Syntax_node5(v___x_249_, v___y_265_, v___y_262_, v___y_254_, v___y_268_, v___x_281_, v___y_273_);
lean_inc_n(v___y_260_, 3);
v___x_283_ = l_Lean_Syntax_node2(v___x_249_, v___y_260_, v___y_266_, v___x_282_);
v___x_284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2));
lean_inc_ref_n(v___y_257_, 3);
v___x_285_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___y_257_, v___x_284_);
v___x_286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3));
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_249_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4));
v___x_289_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___y_257_, v___x_288_);
v___x_290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5));
v___x_291_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___y_257_, v___x_290_);
v___x_292_ = l_Lean_Syntax_node1(v___x_249_, v___x_291_, v___y_273_);
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6));
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7));
v___x_295_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___x_293_, v___x_294_);
v___x_296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9);
v___x_297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10));
lean_inc(v_a_243_);
lean_inc(v___y_269_);
v___x_298_ = l_Lean_addMacroScope(v___y_269_, v___x_297_, v_a_243_);
lean_inc(v___y_259_);
v___x_299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_299_, 0, v___x_249_);
lean_ctor_set(v___x_299_, 1, v___x_296_);
lean_ctor_set(v___x_299_, 2, v___x_298_);
lean_ctor_set(v___x_299_, 3, v___y_259_);
v___x_300_ = l_Lean_Syntax_node1(v___x_249_, v___y_267_, v___y_272_);
v___x_301_ = l_Lean_Syntax_node2(v___x_249_, v___x_295_, v___x_299_, v___x_300_);
lean_inc(v___x_292_);
v___x_302_ = l_Lean_Syntax_node2(v___x_249_, v___x_289_, v___x_292_, v___x_301_);
v___x_303_ = l_Lean_Syntax_node1(v___x_249_, v___y_267_, v___x_302_);
v___x_304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11));
v___x_305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_249_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_Syntax_node3(v___x_249_, v___x_285_, v___x_287_, v___x_303_, v___x_305_);
v___x_307_ = l_Lean_Syntax_node1(v___x_249_, v___y_267_, v___x_306_);
lean_inc(v___y_253_);
v___x_308_ = l_Lean_Syntax_node7(v___x_249_, v___y_253_, v___y_273_, v___x_307_, v___y_273_, v___y_273_, v___y_273_, v___y_273_, v___y_273_);
v___x_309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12));
lean_inc_ref_n(v___y_271_, 3);
v___x_310_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___y_271_, v___x_309_);
v___x_311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_249_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
v___x_312_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14);
v___x_313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15));
v___x_314_ = l_Lean_addMacroScope(v___y_269_, v___x_313_, v_a_243_);
v___x_315_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_315_, 0, v___x_249_);
lean_ctor_set(v___x_315_, 1, v___x_312_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
lean_ctor_set(v___x_315_, 3, v___y_259_);
lean_inc_ref(v___x_315_);
v___x_316_ = l_Lean_Syntax_node2(v___x_249_, v___y_256_, v___x_315_, v___y_273_);
v___x_317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16));
v___x_318_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___y_271_, v___x_317_);
v___x_319_ = l_Lean_Syntax_node2(v___x_249_, v___x_318_, v___y_273_, v___y_255_);
lean_inc(v___x_319_);
v___x_320_ = l_Lean_Syntax_node4(v___x_249_, v___x_310_, v___x_311_, v___x_316_, v___x_319_, v___y_273_);
v___x_321_ = l_Lean_Syntax_node2(v___x_249_, v___y_260_, v___x_308_, v___x_320_);
v___x_322_ = l_Lean_Syntax_node7(v___x_249_, v___y_253_, v___y_273_, v___y_273_, v___y_273_, v___y_273_, v___y_273_, v___y_273_, v___y_273_);
v___x_323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17));
v___x_324_ = l_Lean_Name_mkStr4(v___y_252_, v___y_270_, v___y_271_, v___x_323_);
v___x_325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_249_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
v___x_326_ = l_Lean_Syntax_node4(v___x_249_, v___y_258_, v___y_264_, v___x_315_, v___x_280_, v___y_273_);
v___x_327_ = l_Lean_Syntax_node6(v___x_249_, v___x_324_, v___x_292_, v___x_325_, v___y_273_, v___y_273_, v___x_319_, v___x_326_);
v___x_328_ = l_Lean_Syntax_node2(v___x_249_, v___y_260_, v___x_322_, v___x_327_);
v___x_329_ = l_Lean_Syntax_node3(v___x_249_, v___y_267_, v___x_283_, v___x_321_, v___x_328_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_329_);
v___x_331_ = v___x_245_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19));
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20));
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21));
v___x_338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22));
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24));
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26));
v___x_341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27);
lean_inc_n(v___x_249_, 23);
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_249_);
lean_ctor_set(v___x_342_, 1, v___x_335_);
lean_ctor_set(v___x_342_, 2, v___x_341_);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28));
v___x_344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29));
v___x_345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_249_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
v___x_346_ = l_Lean_Syntax_node1(v___x_249_, v___x_344_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node1(v___x_249_, v___x_335_, v___x_346_);
lean_inc_ref_n(v___x_342_, 8);
v___x_348_ = l_Lean_Syntax_node7(v___x_249_, v___x_340_, v___x_342_, v___x_342_, v___x_342_, v___x_342_, v___x_342_, v___x_347_, v___x_342_);
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31));
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32));
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_249_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34));
v___x_353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36);
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37));
lean_inc_n(v_a_243_, 3);
lean_inc_n(v_a_334_, 3);
v___x_355_ = l_Lean_addMacroScope(v_a_334_, v___x_354_, v_a_243_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_357_, 0, v___x_249_);
lean_ctor_set(v___x_357_, 1, v___x_353_);
lean_ctor_set(v___x_357_, 2, v___x_355_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_inc_ref(v___x_357_);
v___x_358_ = l_Lean_Syntax_node2(v___x_249_, v___x_352_, v___x_357_, v___x_342_);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39));
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40));
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42));
v___x_362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43));
v___x_363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_249_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45));
v___x_365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48));
v___x_367_ = l_Lean_addMacroScope(v_a_334_, v___x_366_, v_a_243_);
v___x_368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52));
v___x_369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_369_, 0, v___x_249_);
lean_ctor_set(v___x_369_, 1, v___x_365_);
lean_ctor_set(v___x_369_, 2, v___x_367_);
lean_ctor_set(v___x_369_, 3, v___x_368_);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54));
v___x_371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55));
v___x_372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_249_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
lean_inc_n(v_a_236_, 2);
v___x_373_ = l_Lean_mkCIdent(v_a_236_);
v___x_374_ = l_Lean_Syntax_node2(v___x_249_, v___x_370_, v___x_372_, v___x_373_);
v___x_375_ = l_Lean_Syntax_node1(v___x_249_, v___x_335_, v___x_374_);
v___x_376_ = l_Lean_Syntax_node2(v___x_249_, v___x_364_, v___x_369_, v___x_375_);
v___x_377_ = l_Lean_Syntax_node2(v___x_249_, v___x_361_, v___x_363_, v___x_376_);
lean_inc(v___x_377_);
v___x_378_ = l_Lean_Syntax_node1(v___x_249_, v___x_335_, v___x_377_);
v___x_379_ = l_Lean_Syntax_node2(v___x_249_, v___x_359_, v___x_342_, v___x_378_);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57));
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58));
v___x_382_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_249_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60));
v___x_384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61));
v___x_385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_249_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63);
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64));
v___x_388_ = l_Lean_addMacroScope(v_a_334_, v___x_387_, v_a_243_);
v___x_389_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_389_, 0, v___x_249_);
lean_ctor_set(v___x_389_, 1, v___x_386_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_ctor_set(v___x_389_, 3, v___x_356_);
v___x_390_ = l_Lean_Syntax_node2(v___x_249_, v___x_383_, v___x_385_, v___x_389_);
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66));
v___x_392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67));
v___x_393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_249_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = l_Lean_Syntax_node1(v___x_249_, v___x_391_, v___x_393_);
v___x_395_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_356_, v_a_236_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_quoteNameMk(v_a_236_);
v___y_251_ = v___x_394_;
v___y_252_ = v___x_336_;
v___y_253_ = v___x_340_;
v___y_254_ = v___x_358_;
v___y_255_ = v___x_377_;
v___y_256_ = v___x_352_;
v___y_257_ = v___x_360_;
v___y_258_ = v___x_380_;
v___y_259_ = v___x_356_;
v___y_260_ = v___x_339_;
v___y_261_ = v___x_364_;
v___y_262_ = v___x_351_;
v___y_263_ = v___x_390_;
v___y_264_ = v___x_382_;
v___y_265_ = v___x_349_;
v___y_266_ = v___x_348_;
v___y_267_ = v___x_335_;
v___y_268_ = v___x_379_;
v___y_269_ = v_a_334_;
v___y_270_ = v___x_337_;
v___y_271_ = v___x_338_;
v___y_272_ = v___x_357_;
v___y_273_ = v___x_342_;
v___y_274_ = v___x_396_;
goto v___jp_250_;
}
else
{
lean_object* v_val_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_a_236_);
v_val_397_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_395_, 1);
v___x_398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69));
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70));
v___x_400_ = lean_string_intercalate(v___x_384_, v_val_397_);
v___x_401_ = lean_string_append(v___x_399_, v___x_400_);
lean_dec_ref(v___x_400_);
v___x_402_ = lean_box(2);
v___x_403_ = l_Lean_Syntax_mkNameLit(v___x_401_, v___x_402_);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
v___x_406_ = lean_array_push(v___x_405_, v___x_403_);
v___x_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_398_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
v___y_251_ = v___x_394_;
v___y_252_ = v___x_336_;
v___y_253_ = v___x_340_;
v___y_254_ = v___x_358_;
v___y_255_ = v___x_377_;
v___y_256_ = v___x_352_;
v___y_257_ = v___x_360_;
v___y_258_ = v___x_380_;
v___y_259_ = v___x_356_;
v___y_260_ = v___x_339_;
v___y_261_ = v___x_364_;
v___y_262_ = v___x_351_;
v___y_263_ = v___x_390_;
v___y_264_ = v___x_382_;
v___y_265_ = v___x_349_;
v___y_266_ = v___x_348_;
v___y_267_ = v___x_335_;
v___y_268_ = v___x_379_;
v___y_269_ = v_a_334_;
v___y_270_ = v___x_337_;
v___y_271_ = v___x_338_;
v___y_272_ = v___x_357_;
v___y_273_ = v___x_342_;
v___y_274_ = v___x_407_;
goto v___jp_250_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_a_241_);
lean_dec_ref(v___y_237_);
lean_dec(v_a_236_);
v_a_420_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_242_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_242_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v___y_237_);
lean_dec(v_a_236_);
v_a_428_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_240_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_240_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___boxed(lean_object* v_a_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1(v_a_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
return v_res_440_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_441_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__0);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
lean_ctor_set(v___x_446_, 3, v___x_445_);
lean_ctor_set(v___x_446_, 4, v___x_444_);
lean_ctor_set(v___x_446_, 5, v___x_444_);
lean_ctor_set(v___x_446_, 6, v___x_444_);
lean_ctor_set(v___x_446_, 7, v___x_444_);
lean_ctor_set(v___x_446_, 8, v___x_444_);
lean_ctor_set(v___x_446_, 9, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(32u);
v___x_448_ = lean_mk_empty_array_with_capacity(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((size_t)5ULL);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_unsigned_to_nat(32u);
v___x_453_ = lean_mk_empty_array_with_capacity(v___x_452_);
v___x_454_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__3);
v___x_455_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_451_);
lean_ctor_set(v___x_455_, 3, v___x_451_);
lean_ctor_set_usize(v___x_455_, 4, v___x_450_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = lean_box(1);
v___x_457_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__4);
v___x_458_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__1);
v___x_459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
lean_ctor_set(v___x_459_, 2, v___x_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(lean_object* v_msgData_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; lean_object* v_env_464_; lean_object* v___x_465_; lean_object* v_scopes_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_opts_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_463_ = lean_st_ref_get(v___y_461_);
v_env_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_env_464_);
lean_dec(v___x_463_);
v___x_465_ = lean_st_ref_get(v___y_461_);
v_scopes_466_ = lean_ctor_get(v___x_465_, 2);
lean_inc(v_scopes_466_);
lean_dec(v___x_465_);
v___x_467_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_468_ = l_List_head_x21___redArg(v___x_467_, v_scopes_466_);
lean_dec(v_scopes_466_);
v_opts_469_ = lean_ctor_get(v___x_468_, 1);
lean_inc_ref(v_opts_469_);
lean_dec(v___x_468_);
v___x_470_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2);
v___x_471_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5);
v___x_472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_472_, 0, v_env_464_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
lean_ctor_set(v___x_472_, 3, v_opts_469_);
v___x_473_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_msgData_460_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msgData_475_, v___y_476_);
lean_dec(v___y_476_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(lean_object* v_opts_479_, lean_object* v_opt_480_){
_start:
{
lean_object* v_name_481_; lean_object* v_defValue_482_; lean_object* v_map_483_; lean_object* v___x_484_; 
v_name_481_ = lean_ctor_get(v_opt_480_, 0);
v_defValue_482_ = lean_ctor_get(v_opt_480_, 1);
v_map_483_ = lean_ctor_get(v_opts_479_, 0);
v___x_484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_483_, v_name_481_);
if (lean_obj_tag(v___x_484_) == 0)
{
uint8_t v___x_485_; 
v___x_485_ = lean_unbox(v_defValue_482_);
return v___x_485_;
}
else
{
lean_object* v_val_486_; 
v_val_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_484_, 1);
if (lean_obj_tag(v_val_486_) == 1)
{
uint8_t v_v_487_; 
v_v_487_ = lean_ctor_get_uint8(v_val_486_, 0);
lean_dec_ref_known(v_val_486_, 0);
return v_v_487_;
}
else
{
uint8_t v___x_488_; 
lean_dec(v_val_486_);
v___x_488_ = lean_unbox(v_defValue_482_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_489_, lean_object* v_opt_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(v_opts_489_, v_opt_490_);
lean_dec_ref(v_opt_490_);
lean_dec_ref(v_opts_489_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_box(1);
v___x_494_ = l_Lean_MessageData_ofFormat(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2));
v___x_499_ = l_Lean_MessageData_ofFormat(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
return v_x_500_;
}
else
{
lean_object* v_head_502_; lean_object* v_tail_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_525_; 
v_head_502_ = lean_ctor_get(v_x_501_, 0);
v_tail_503_ = lean_ctor_get(v_x_501_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_525_ == 0)
{
v___x_505_ = v_x_501_;
v_isShared_506_ = v_isSharedCheck_525_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_tail_503_);
lean_inc(v_head_502_);
lean_dec(v_x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_525_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_before_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_523_; 
v_before_507_ = lean_ctor_get(v_head_502_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_head_502_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_head_502_, 1);
lean_dec(v_unused_524_);
v___x_509_ = v_head_502_;
v_isShared_510_ = v_isSharedCheck_523_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_before_507_);
lean_dec(v_head_502_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_523_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 7);
lean_ctor_set(v___x_509_, 1, v___x_511_);
lean_ctor_set(v___x_509_, 0, v_x_500_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_x_500_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_522_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 7);
lean_ctor_set(v___x_505_, 1, v___x_514_);
lean_ctor_set(v___x_505_, 0, v___x_513_);
v___x_516_ = v___x_505_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_521_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = l_Lean_MessageData_ofSyntax(v_before_507_);
v___x_518_ = l_Lean_indentD(v___x_517_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_516_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v_x_500_ = v___x_519_;
v_x_501_ = v_tail_503_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1));
v___x_530_ = l_Lean_MessageData_ofFormat(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(lean_object* v_msgData_531_, lean_object* v_macroStack_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_scopes_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_opts_539_; lean_object* v___x_540_; uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_535_ = lean_st_ref_get(v___y_533_);
v_scopes_536_ = lean_ctor_get(v___x_535_, 2);
lean_inc(v_scopes_536_);
lean_dec(v___x_535_);
v___x_537_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_538_ = l_List_head_x21___redArg(v___x_537_, v_scopes_536_);
lean_dec(v_scopes_536_);
v_opts_539_ = lean_ctor_get(v___x_538_, 1);
lean_inc_ref(v_opts_539_);
lean_dec(v___x_538_);
v___x_540_ = l_Lean_Elab_pp_macroStack;
v___x_541_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(v_opts_539_, v___x_540_);
lean_dec_ref(v_opts_539_);
v___x_542_ = lean_bool_not(v___x_541_);
if (v___x_542_ == 0)
{
if (lean_obj_tag(v_macroStack_532_) == 0)
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_msgData_531_);
return v___x_543_;
}
else
{
lean_object* v_head_544_; lean_object* v_after_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_560_; 
v_head_544_ = lean_ctor_get(v_macroStack_532_, 0);
lean_inc(v_head_544_);
v_after_545_ = lean_ctor_get(v_head_544_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_head_544_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_head_544_, 0);
lean_dec(v_unused_561_);
v___x_547_ = v_head_544_;
v_isShared_548_ = v_isSharedCheck_560_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_after_545_);
lean_dec(v_head_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_560_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 7);
lean_ctor_set(v___x_547_, 1, v___x_549_);
lean_ctor_set(v___x_547_, 0, v_msgData_531_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_msgData_531_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_559_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_msgData_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_552_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_MessageData_ofSyntax(v_after_545_);
v___x_555_ = l_Lean_indentD(v___x_554_);
v_msgData_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_556_, 0, v___x_553_);
lean_ctor_set(v_msgData_556_, 1, v___x_555_);
v___x_557_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(v_msgData_556_, v_macroStack_532_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
}
else
{
lean_object* v___x_562_; 
lean_dec(v_macroStack_532_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_msgData_531_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_563_, lean_object* v_macroStack_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_msgData_563_, v_macroStack_564_, v___y_565_);
lean_dec(v___y_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Elab_Command_getRef___redArg(v___y_569_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v_macroStack_574_; lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v_macroStack_574_ = lean_ctor_get(v___y_569_, 4);
v___x_575_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msg_568_, v___y_570_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = l_Lean_Elab_getBetterRef(v_a_573_, v_macroStack_574_);
lean_dec(v_a_573_);
lean_inc(v_macroStack_574_);
v___x_578_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_a_576_, v_macroStack_574_, v___y_570_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_587_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_577_);
lean_ctor_set(v___x_583_, 1, v_a_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 1);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_msg_568_);
v_a_588_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_572_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_572_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg___boxed(lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(lean_object* v_ref_601_, lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Elab_Command_getRef___redArg(v___y_603_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v_fileName_608_; lean_object* v_fileMap_609_; lean_object* v_currRecDepth_610_; lean_object* v_cmdPos_611_; lean_object* v_macroStack_612_; lean_object* v_quotContext_x3f_613_; lean_object* v_currMacroScope_614_; lean_object* v_snap_x3f_615_; lean_object* v_cancelTk_x3f_616_; uint8_t v_suppressElabErrors_617_; lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v_fileName_608_ = lean_ctor_get(v___y_603_, 0);
v_fileMap_609_ = lean_ctor_get(v___y_603_, 1);
v_currRecDepth_610_ = lean_ctor_get(v___y_603_, 2);
v_cmdPos_611_ = lean_ctor_get(v___y_603_, 3);
v_macroStack_612_ = lean_ctor_get(v___y_603_, 4);
v_quotContext_x3f_613_ = lean_ctor_get(v___y_603_, 5);
v_currMacroScope_614_ = lean_ctor_get(v___y_603_, 6);
v_snap_x3f_615_ = lean_ctor_get(v___y_603_, 8);
v_cancelTk_x3f_616_ = lean_ctor_get(v___y_603_, 9);
v_suppressElabErrors_617_ = lean_ctor_get_uint8(v___y_603_, sizeof(void*)*10);
v_ref_618_ = l_Lean_replaceRef(v_ref_601_, v_a_607_);
lean_dec(v_a_607_);
lean_inc(v_cancelTk_x3f_616_);
lean_inc(v_snap_x3f_615_);
lean_inc(v_currMacroScope_614_);
lean_inc(v_quotContext_x3f_613_);
lean_inc(v_macroStack_612_);
lean_inc(v_cmdPos_611_);
lean_inc(v_currRecDepth_610_);
lean_inc_ref(v_fileMap_609_);
lean_inc_ref(v_fileName_608_);
v___x_619_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_619_, 0, v_fileName_608_);
lean_ctor_set(v___x_619_, 1, v_fileMap_609_);
lean_ctor_set(v___x_619_, 2, v_currRecDepth_610_);
lean_ctor_set(v___x_619_, 3, v_cmdPos_611_);
lean_ctor_set(v___x_619_, 4, v_macroStack_612_);
lean_ctor_set(v___x_619_, 5, v_quotContext_x3f_613_);
lean_ctor_set(v___x_619_, 6, v_currMacroScope_614_);
lean_ctor_set(v___x_619_, 7, v_ref_618_);
lean_ctor_set(v___x_619_, 8, v_snap_x3f_615_);
lean_ctor_set(v___x_619_, 9, v_cancelTk_x3f_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*10, v_suppressElabErrors_617_);
v___x_620_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_602_, v___x_619_, v___y_604_);
lean_dec_ref_known(v___x_619_, 10);
return v___x_620_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_msg_602_);
v_a_621_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_606_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_606_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_ref_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_629_, v_msg_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v_ref_629_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0));
v___x_637_ = l_Lean_stringToMessageData(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12));
v___x_655_ = l_Lean_stringToMessageData(v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(lean_object* v_msg_656_, lean_object* v_declHint_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_env_661_; uint8_t v___y_663_; uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_660_ = lean_st_ref_get(v___y_658_);
v_env_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_env_661_);
lean_dec(v___x_660_);
v___x_719_ = l_Lean_Name_isAnonymous(v_declHint_657_);
v___x_720_ = lean_bool_not(v___x_719_);
if (v___x_720_ == 0)
{
v___y_663_ = v___x_720_;
goto v___jp_662_;
}
else
{
uint8_t v_isExporting_721_; 
v_isExporting_721_ = lean_ctor_get_uint8(v_env_661_, sizeof(void*)*8);
v___y_663_ = v_isExporting_721_;
goto v___jp_662_;
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v_env_661_);
lean_dec(v_declHint_657_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v_msg_656_);
return v___x_664_;
}
else
{
uint8_t v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = 0;
lean_inc_ref(v_env_661_);
v___x_666_ = l_Lean_Environment_setExporting(v_env_661_, v___x_665_);
lean_inc(v_declHint_657_);
lean_inc_ref(v___x_666_);
v___x_667_ = l_Lean_Environment_contains(v___x_666_, v_declHint_657_, v___y_663_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec_ref(v___x_666_);
lean_dec_ref(v_env_661_);
lean_dec(v_declHint_657_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_msg_656_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_c_674_; lean_object* v___x_675_; 
v___x_669_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2);
v___x_670_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5);
v___x_671_ = l_Lean_Options_empty;
v___x_672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_672_, 0, v___x_666_);
lean_ctor_set(v___x_672_, 1, v___x_669_);
lean_ctor_set(v___x_672_, 2, v___x_670_);
lean_ctor_set(v___x_672_, 3, v___x_671_);
lean_inc(v_declHint_657_);
v___x_673_ = l_Lean_MessageData_ofConstName(v_declHint_657_, v___x_665_);
v_c_674_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_674_, 0, v___x_672_);
lean_ctor_set(v_c_674_, 1, v___x_673_);
v___x_675_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_661_, v_declHint_657_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_env_661_);
lean_dec(v_declHint_657_);
v___x_676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_c_674_);
v___x_678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Lean_MessageData_note(v___x_679_);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v_msg_656_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v_val_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_718_; 
v_val_683_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_718_ == 0)
{
v___x_685_ = v___x_675_;
v_isShared_686_ = v_isSharedCheck_718_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_val_683_);
lean_dec(v___x_675_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_718_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_mod_690_; uint8_t v___x_691_; 
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_Environment_header(v_env_661_);
lean_dec_ref(v_env_661_);
v___x_689_ = l_Lean_EnvironmentHeader_moduleNames(v___x_688_);
v_mod_690_ = lean_array_get(v___x_687_, v___x_689_, v_val_683_);
lean_dec(v_val_683_);
lean_dec_ref(v___x_689_);
v___x_691_ = l_Lean_isPrivateName(v_declHint_657_);
lean_dec(v_declHint_657_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v_c_674_);
v___x_694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_MessageData_ofName(v_mod_690_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_MessageData_note(v___x_699_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v_msg_656_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 0);
lean_ctor_set(v___x_685_, 0, v___x_701_);
v___x_703_ = v___x_685_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_c_674_);
v___x_707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = l_Lean_MessageData_ofName(v_mod_690_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_MessageData_note(v___x_712_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v_msg_656_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 0);
lean_ctor_set(v___x_685_, 0, v___x_714_);
v___x_716_ = v___x_685_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___boxed(lean_object* v_msg_722_, lean_object* v_declHint_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_722_, v_declHint_723_, v___y_724_);
lean_dec(v___y_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(lean_object* v_msg_727_, lean_object* v_declHint_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_742_; 
v___x_732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_727_, v_declHint_728_, v___y_730_);
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_742_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_737_ = l_Lean_unknownIdentifierMessageTag;
v___x_738_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v_a_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_738_);
v___x_740_ = v___x_735_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_msg_743_, lean_object* v_declHint_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(v_msg_743_, v_declHint_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(lean_object* v_ref_749_, lean_object* v_msg_750_, lean_object* v_declHint_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; lean_object* v_a_756_; lean_object* v___x_757_; 
v___x_755_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(v_msg_750_, v_declHint_751_, v___y_752_, v___y_753_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v___x_757_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_749_, v_a_756_, v___y_752_, v___y_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_ref_758_, lean_object* v_msg_759_, lean_object* v_declHint_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_758_, v_msg_759_, v_declHint_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v_ref_758_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_770_, lean_object* v_constName_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_775_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1);
v___x_776_ = 0;
lean_inc(v_constName_771_);
v___x_777_ = l_Lean_MessageData_ofConstName(v_constName_771_, v___x_776_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_775_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_770_, v___x_780_, v_constName_771_, v___y_772_, v___y_773_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_782_, lean_object* v_constName_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_ref_782_, v_constName_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v_ref_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(lean_object* v_constName_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Elab_Command_getRef___redArg(v___y_789_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_a_793_, v_constName_788_, v___y_789_, v___y_790_);
lean_dec(v_a_793_);
return v___x_794_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_constName_788_);
v_a_795_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_792_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_792_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg___boxed(lean_object* v_constName_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(lean_object* v_constName_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v_env_813_; uint8_t v___x_814_; lean_object* v___x_815_; 
v___x_812_ = lean_st_ref_get(v___y_810_);
v_env_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_env_813_);
lean_dec(v___x_812_);
v___x_814_ = 0;
lean_inc(v_constName_808_);
v___x_815_ = l_Lean_Environment_find_x3f(v_env_813_, v_constName_808_, v___x_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_808_, v___y_809_, v___y_810_);
return v___x_816_;
}
else
{
lean_object* v_val_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_constName_808_);
v_val_817_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_815_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_val_817_);
lean_dec(v___x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_val_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2___boxed(lean_object* v_constName_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(v_constName_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(lean_object* v_as_834_, size_t v_sz_835_, size_t v_i_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = lean_usize_dec_lt(v_i_836_, v_sz_835_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v_b_837_);
return v___x_842_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_array_uget_borrowed(v_as_834_, v_i_836_);
lean_inc(v_a_843_);
v___x_844_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(v_a_843_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___f_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0));
v___x_847_ = lean_box(0);
lean_inc(v_a_843_);
v___f_848_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___boxed), 4, 1);
lean_closure_set(v___f_848_, 0, v_a_843_);
v___f_849_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2___boxed), 4, 1);
lean_closure_set(v___f_849_, 0, v___f_848_);
v___x_857_ = l_Lean_ConstantInfo_levelParams(v_a_845_);
lean_dec(v_a_845_);
v___x_858_ = l_List_isEmpty___redArg(v___x_857_);
lean_dec(v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_inc(v_a_843_);
v___x_859_ = l_Lean_MessageData_ofConstName(v_a_843_, v___x_858_);
v___x_860_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v___x_861_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_dec_ref_known(v___x_862_, 1);
v___y_851_ = v___y_838_;
v___y_852_ = v___y_839_;
goto v___jp_850_;
}
else
{
lean_dec_ref(v___f_849_);
return v___x_862_;
}
}
else
{
v___y_851_ = v___y_838_;
v___y_852_ = v___y_839_;
goto v___jp_850_;
}
v___jp_850_:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Elab_Command_withScope___redArg(v___f_846_, v___f_849_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
size_t v___x_854_; size_t v___x_855_; 
lean_dec_ref_known(v___x_853_, 1);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_836_, v___x_854_);
v_i_836_ = v___x_855_;
v_b_837_ = v___x_847_;
goto _start;
}
else
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_844_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_844_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___boxed(lean_object* v_as_871_, lean_object* v_sz_872_, lean_object* v_i_873_, lean_object* v_b_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
size_t v_sz_boxed_878_; size_t v_i_boxed_879_; lean_object* v_res_880_; 
v_sz_boxed_878_ = lean_unbox_usize(v_sz_872_);
lean_dec(v_sz_872_);
v_i_boxed_879_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(v_as_871_, v_sz_boxed_878_, v_i_boxed_879_, v_b_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec_ref(v_as_871_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(lean_object* v_declNames_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; 
v___x_885_ = lean_box(0);
v_sz_886_ = lean_array_size(v_declNames_881_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(v_declNames_881_, v_sz_886_, v___x_887_, v___x_885_, v_a_882_, v_a_883_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_897_; 
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_898_);
v___x_890_ = v___x_888_;
v_isShared_891_ = v_isSharedCheck_897_;
goto v_resetjp_889_;
}
else
{
lean_dec(v___x_888_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_897_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_892_ = 1;
v___x_893_ = lean_box(v___x_892_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_888_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_888_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed(lean_object* v_declNames_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(v_declNames_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v_declNames_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(lean_object* v_msgData_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msgData_912_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___boxed(lean_object* v_msgData_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(v_msgData_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(lean_object* v_00_u03b1_922_, lean_object* v_msg_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___boxed(lean_object* v_00_u03b1_928_, lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(v_00_u03b1_928_, v_msg_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(lean_object* v_00_u03b1_934_, lean_object* v_constName_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_935_, v___y_936_, v___y_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___boxed(lean_object* v_00_u03b1_940_, lean_object* v_constName_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(v_00_u03b1_940_, v_constName_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(lean_object* v_msgData_946_, lean_object* v_macroStack_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_msgData_946_, v_macroStack_947_, v___y_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___boxed(lean_object* v_msgData_952_, lean_object* v_macroStack_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(v_msgData_952_, v_macroStack_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_958_, lean_object* v_ref_959_, lean_object* v_constName_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_ref_959_, v_constName_960_, v___y_961_, v___y_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_965_, lean_object* v_ref_966_, lean_object* v_constName_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(v_00_u03b1_965_, v_ref_966_, v_constName_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_ref_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(lean_object* v_00_u03b1_972_, lean_object* v_ref_973_, lean_object* v_msg_974_, lean_object* v_declHint_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_973_, v_msg_974_, v_declHint_975_, v___y_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b1_980_, lean_object* v_ref_981_, lean_object* v_msg_982_, lean_object* v_declHint_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(v_00_u03b1_980_, v_ref_981_, v_msg_982_, v_declHint_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v_ref_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(lean_object* v_msg_988_, lean_object* v_declHint_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_988_, v_declHint_989_, v___y_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___boxed(lean_object* v_msg_994_, lean_object* v_declHint_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(v_msg_994_, v_declHint_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(lean_object* v_00_u03b1_1000_, lean_object* v_ref_1001_, lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_1001_, v_msg_1002_, v___y_1003_, v___y_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_ref_1008_, lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(v_00_u03b1_1007_, v_ref_1008_, v_msg_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v_ref_1008_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48));
v___x_1017_ = ((lean_object*)(l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_));
v___x_1018_ = l_Lean_Elab_registerDerivingHandler(v___x_1016_, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2____boxed(lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_();
return v_res_1020_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_TypeName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_TypeName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_TypeName(builtin);
}
#ifdef __cplusplus
}
#endif
