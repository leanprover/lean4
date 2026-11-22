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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__21;
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
v___x_135_ = l_Array_mkArray0___redArg();
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
lean_object* v_a_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = 0;
v___x_243_ = l_Lean_SourceInfo_fromRef(v_a_241_, v___x_242_);
lean_dec(v_a_241_);
v___x_244_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_237_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_419_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_419_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_419_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_419_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v_a_333_; lean_object* v_quotContext_x3f_407_; 
v_quotContext_x3f_407_ = lean_ctor_get(v___y_237_, 5);
lean_inc(v_quotContext_x3f_407_);
lean_dec_ref(v___y_237_);
if (lean_obj_tag(v_quotContext_x3f_407_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_getMainModule___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__1___redArg(v___y_238_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_a_333_ = v_a_409_;
goto v___jp_332_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_247_);
lean_dec(v_a_245_);
lean_dec(v___x_243_);
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
v_val_418_ = lean_ctor_get(v_quotContext_x3f_407_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_quotContext_x3f_407_, 1);
v_a_333_ = v_val_418_;
goto v___jp_332_;
}
v___jp_249_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc_n(v___y_253_, 4);
lean_inc_n(v___x_243_, 28);
v___x_274_ = l_Lean_Syntax_node2(v___x_243_, v___y_253_, v___y_262_, v___y_273_);
v___x_275_ = l_Lean_Syntax_node2(v___x_243_, v___y_261_, v___y_271_, v___x_274_);
v___x_276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__0));
v___x_277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__1));
lean_inc_ref_n(v___y_265_, 8);
lean_inc_ref_n(v___y_269_, 8);
v___x_278_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___x_276_, v___x_277_);
lean_inc_n(v___y_270_, 23);
v___x_279_ = l_Lean_Syntax_node2(v___x_243_, v___x_278_, v___y_270_, v___y_270_);
lean_inc(v___x_279_);
lean_inc(v___y_257_);
lean_inc_n(v___y_264_, 2);
v___x_280_ = l_Lean_Syntax_node4(v___x_243_, v___y_264_, v___y_257_, v___x_275_, v___x_279_, v___y_270_);
lean_inc(v___y_258_);
v___x_281_ = l_Lean_Syntax_node5(v___x_243_, v___y_258_, v___y_272_, v___y_263_, v___y_254_, v___x_280_, v___y_270_);
lean_inc_n(v___y_252_, 3);
v___x_282_ = l_Lean_Syntax_node2(v___x_243_, v___y_252_, v___y_259_, v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__2));
lean_inc_ref_n(v___y_255_, 3);
v___x_284_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___y_255_, v___x_283_);
v___x_285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__3));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_243_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__4));
v___x_288_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___y_255_, v___x_287_);
v___x_289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__5));
v___x_290_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___y_255_, v___x_289_);
v___x_291_ = l_Lean_Syntax_node1(v___x_243_, v___x_290_, v___y_270_);
v___x_292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__6));
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__7));
v___x_294_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___x_292_, v___x_293_);
v___x_295_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__9);
v___x_296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__10));
lean_inc(v_a_245_);
lean_inc(v___y_251_);
v___x_297_ = l_Lean_addMacroScope(v___y_251_, v___x_296_, v_a_245_);
lean_inc(v___y_268_);
v___x_298_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_298_, 0, v___x_243_);
lean_ctor_set(v___x_298_, 1, v___x_295_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
lean_ctor_set(v___x_298_, 3, v___y_268_);
v___x_299_ = l_Lean_Syntax_node1(v___x_243_, v___y_253_, v___y_267_);
v___x_300_ = l_Lean_Syntax_node2(v___x_243_, v___x_294_, v___x_298_, v___x_299_);
lean_inc(v___x_291_);
v___x_301_ = l_Lean_Syntax_node2(v___x_243_, v___x_288_, v___x_291_, v___x_300_);
v___x_302_ = l_Lean_Syntax_node1(v___x_243_, v___y_253_, v___x_301_);
v___x_303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__11));
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_243_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_Syntax_node3(v___x_243_, v___x_284_, v___x_286_, v___x_302_, v___x_304_);
v___x_306_ = l_Lean_Syntax_node1(v___x_243_, v___y_253_, v___x_305_);
lean_inc(v___y_266_);
v___x_307_ = l_Lean_Syntax_node7(v___x_243_, v___y_266_, v___y_270_, v___x_306_, v___y_270_, v___y_270_, v___y_270_, v___y_270_, v___y_270_);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__12));
lean_inc_ref_n(v___y_250_, 3);
v___x_309_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___y_250_, v___x_308_);
v___x_310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_243_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
v___x_311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__14);
v___x_312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__15));
v___x_313_ = l_Lean_addMacroScope(v___y_251_, v___x_312_, v_a_245_);
v___x_314_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_314_, 0, v___x_243_);
lean_ctor_set(v___x_314_, 1, v___x_311_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_ctor_set(v___x_314_, 3, v___y_268_);
lean_inc_ref(v___x_314_);
v___x_315_ = l_Lean_Syntax_node2(v___x_243_, v___y_260_, v___x_314_, v___y_270_);
v___x_316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__16));
v___x_317_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___y_250_, v___x_316_);
v___x_318_ = l_Lean_Syntax_node2(v___x_243_, v___x_317_, v___y_270_, v___y_256_);
lean_inc(v___x_318_);
v___x_319_ = l_Lean_Syntax_node4(v___x_243_, v___x_309_, v___x_310_, v___x_315_, v___x_318_, v___y_270_);
v___x_320_ = l_Lean_Syntax_node2(v___x_243_, v___y_252_, v___x_307_, v___x_319_);
v___x_321_ = l_Lean_Syntax_node7(v___x_243_, v___y_266_, v___y_270_, v___y_270_, v___y_270_, v___y_270_, v___y_270_, v___y_270_, v___y_270_);
v___x_322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__17));
v___x_323_ = l_Lean_Name_mkStr4(v___y_269_, v___y_265_, v___y_250_, v___x_322_);
v___x_324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_243_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
v___x_325_ = l_Lean_Syntax_node4(v___x_243_, v___y_264_, v___y_257_, v___x_314_, v___x_279_, v___y_270_);
v___x_326_ = l_Lean_Syntax_node6(v___x_243_, v___x_323_, v___x_291_, v___x_324_, v___y_270_, v___y_270_, v___x_318_, v___x_325_);
v___x_327_ = l_Lean_Syntax_node2(v___x_243_, v___y_252_, v___x_321_, v___x_326_);
v___x_328_ = l_Lean_Syntax_node3(v___x_243_, v___y_253_, v___x_282_, v___x_320_, v___x_327_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_328_);
v___x_330_ = v___x_247_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__19));
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__20));
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__21));
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__22));
v___x_338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__24));
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__26));
v___x_340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__27);
lean_inc_n(v___x_243_, 23);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v___x_243_);
lean_ctor_set(v___x_341_, 1, v___x_334_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
v___x_342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__28));
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__29));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_243_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
v___x_345_ = l_Lean_Syntax_node1(v___x_243_, v___x_343_, v___x_344_);
v___x_346_ = l_Lean_Syntax_node1(v___x_243_, v___x_334_, v___x_345_);
lean_inc_ref_n(v___x_341_, 8);
v___x_347_ = l_Lean_Syntax_node7(v___x_243_, v___x_339_, v___x_341_, v___x_341_, v___x_341_, v___x_341_, v___x_341_, v___x_346_, v___x_341_);
v___x_348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__31));
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__32));
v___x_350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_243_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__34));
v___x_352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__36);
v___x_353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__37));
lean_inc_n(v_a_245_, 3);
lean_inc_n(v_a_333_, 3);
v___x_354_ = l_Lean_addMacroScope(v_a_333_, v___x_353_, v_a_245_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_356_, 0, v___x_243_);
lean_ctor_set(v___x_356_, 1, v___x_352_);
lean_ctor_set(v___x_356_, 2, v___x_354_);
lean_ctor_set(v___x_356_, 3, v___x_355_);
lean_inc_ref(v___x_356_);
v___x_357_ = l_Lean_Syntax_node2(v___x_243_, v___x_351_, v___x_356_, v___x_341_);
v___x_358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__39));
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__40));
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__42));
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__43));
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_243_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__45));
v___x_364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__47);
v___x_365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48));
v___x_366_ = l_Lean_addMacroScope(v_a_333_, v___x_365_, v_a_245_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__52));
v___x_368_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_368_, 0, v___x_243_);
lean_ctor_set(v___x_368_, 1, v___x_364_);
lean_ctor_set(v___x_368_, 2, v___x_366_);
lean_ctor_set(v___x_368_, 3, v___x_367_);
v___x_369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__54));
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__55));
v___x_371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_243_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
lean_inc_n(v_a_236_, 2);
v___x_372_ = l_Lean_mkCIdent(v_a_236_);
v___x_373_ = l_Lean_Syntax_node2(v___x_243_, v___x_369_, v___x_371_, v___x_372_);
v___x_374_ = l_Lean_Syntax_node1(v___x_243_, v___x_334_, v___x_373_);
v___x_375_ = l_Lean_Syntax_node2(v___x_243_, v___x_363_, v___x_368_, v___x_374_);
v___x_376_ = l_Lean_Syntax_node2(v___x_243_, v___x_360_, v___x_362_, v___x_375_);
lean_inc(v___x_376_);
v___x_377_ = l_Lean_Syntax_node1(v___x_243_, v___x_334_, v___x_376_);
v___x_378_ = l_Lean_Syntax_node2(v___x_243_, v___x_358_, v___x_341_, v___x_377_);
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__57));
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__58));
v___x_381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_243_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__60));
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__61));
v___x_384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_243_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__63);
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__64));
v___x_387_ = l_Lean_addMacroScope(v_a_333_, v___x_386_, v_a_245_);
v___x_388_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_388_, 0, v___x_243_);
lean_ctor_set(v___x_388_, 1, v___x_385_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_ctor_set(v___x_388_, 3, v___x_355_);
v___x_389_ = l_Lean_Syntax_node2(v___x_243_, v___x_382_, v___x_384_, v___x_388_);
v___x_390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__66));
v___x_391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__67));
v___x_392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_243_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_Syntax_node1(v___x_243_, v___x_390_, v___x_392_);
v___x_394_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_355_, v_a_236_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_quoteNameMk(v_a_236_);
v___y_250_ = v___x_337_;
v___y_251_ = v_a_333_;
v___y_252_ = v___x_338_;
v___y_253_ = v___x_334_;
v___y_254_ = v___x_378_;
v___y_255_ = v___x_359_;
v___y_256_ = v___x_376_;
v___y_257_ = v___x_381_;
v___y_258_ = v___x_348_;
v___y_259_ = v___x_347_;
v___y_260_ = v___x_351_;
v___y_261_ = v___x_363_;
v___y_262_ = v___x_393_;
v___y_263_ = v___x_357_;
v___y_264_ = v___x_379_;
v___y_265_ = v___x_336_;
v___y_266_ = v___x_339_;
v___y_267_ = v___x_356_;
v___y_268_ = v___x_355_;
v___y_269_ = v___x_335_;
v___y_270_ = v___x_341_;
v___y_271_ = v___x_389_;
v___y_272_ = v___x_350_;
v___y_273_ = v___x_395_;
goto v___jp_249_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_a_236_);
v_val_396_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_394_, 1);
v___x_397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__69));
v___x_398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70));
v___x_399_ = lean_string_intercalate(v___x_383_, v_val_396_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = lean_box(2);
v___x_402_ = l_Lean_Syntax_mkNameLit(v___x_400_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_mk_empty_array_with_capacity(v___x_403_);
v___x_405_ = lean_array_push(v___x_404_, v___x_402_);
v___x_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_401_);
lean_ctor_set(v___x_406_, 1, v___x_397_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
v___y_250_ = v___x_337_;
v___y_251_ = v_a_333_;
v___y_252_ = v___x_338_;
v___y_253_ = v___x_334_;
v___y_254_ = v___x_378_;
v___y_255_ = v___x_359_;
v___y_256_ = v___x_376_;
v___y_257_ = v___x_381_;
v___y_258_ = v___x_348_;
v___y_259_ = v___x_347_;
v___y_260_ = v___x_351_;
v___y_261_ = v___x_363_;
v___y_262_ = v___x_393_;
v___y_263_ = v___x_357_;
v___y_264_ = v___x_379_;
v___y_265_ = v___x_336_;
v___y_266_ = v___x_339_;
v___y_267_ = v___x_356_;
v___y_268_ = v___x_355_;
v___y_269_ = v___x_335_;
v___y_270_ = v___x_341_;
v___y_271_ = v___x_389_;
v___y_272_ = v___x_350_;
v___y_273_ = v___x_406_;
goto v___jp_249_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v___x_243_);
lean_dec_ref(v___y_237_);
lean_dec(v_a_236_);
v_a_420_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_244_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_244_);
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
v___x_441_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_446_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_446_, 10, v___x_444_);
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
lean_object* v___x_463_; lean_object* v_env_464_; uint8_t v___x_465_; lean_object* v_env_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_scopes_469_; lean_object* v___x_470_; lean_object* v_opts_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_463_ = lean_st_ref_get(v___y_461_);
v_env_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_env_464_);
lean_dec(v___x_463_);
v___x_465_ = 0;
v_env_466_ = l_Lean_Environment_setRecordingDeps(v_env_464_, v___x_465_);
v___x_467_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_468_ = lean_st_ref_get(v___y_461_);
v_scopes_469_ = lean_ctor_get(v___x_468_, 2);
lean_inc(v_scopes_469_);
lean_dec(v___x_468_);
v___x_470_ = l_List_head_x21___redArg(v___x_467_, v_scopes_469_);
lean_dec(v_scopes_469_);
v_opts_471_ = lean_ctor_get(v___x_470_, 1);
lean_inc_ref(v_opts_471_);
lean_dec(v___x_470_);
v___x_472_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2);
v___x_473_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5);
v___x_474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_474_, 0, v_env_466_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
lean_ctor_set(v___x_474_, 3, v_opts_471_);
v___x_475_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_msgData_460_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msgData_477_, v___y_478_);
lean_dec(v___y_478_);
return v_res_480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(lean_object* v_opts_481_, lean_object* v_opt_482_){
_start:
{
lean_object* v_name_483_; lean_object* v_defValue_484_; lean_object* v_map_485_; lean_object* v___x_486_; 
v_name_483_ = lean_ctor_get(v_opt_482_, 0);
v_defValue_484_ = lean_ctor_get(v_opt_482_, 1);
v_map_485_ = lean_ctor_get(v_opts_481_, 0);
v___x_486_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_485_, v_name_483_);
if (lean_obj_tag(v___x_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = lean_unbox(v_defValue_484_);
return v___x_487_;
}
else
{
lean_object* v_val_488_; 
v_val_488_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_486_, 1);
if (lean_obj_tag(v_val_488_) == 1)
{
uint8_t v_v_489_; 
v_v_489_ = lean_ctor_get_uint8(v_val_488_, 0);
lean_dec_ref_known(v_val_488_, 0);
return v_v_489_;
}
else
{
uint8_t v___x_490_; 
lean_dec(v_val_488_);
v___x_490_ = lean_unbox(v_defValue_484_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_491_, lean_object* v_opt_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(v_opts_491_, v_opt_492_);
lean_dec_ref(v_opt_492_);
lean_dec_ref(v_opts_491_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_box(1);
v___x_496_ = l_Lean_MessageData_ofFormat(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__2));
v___x_501_ = l_Lean_MessageData_ofFormat(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
return v_x_502_;
}
else
{
lean_object* v_head_504_; lean_object* v_tail_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_527_; 
v_head_504_ = lean_ctor_get(v_x_503_, 0);
v_tail_505_ = lean_ctor_get(v_x_503_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_503_);
if (v_isSharedCheck_527_ == 0)
{
v___x_507_ = v_x_503_;
v_isShared_508_ = v_isSharedCheck_527_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_tail_505_);
lean_inc(v_head_504_);
lean_dec(v_x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_527_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_before_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_525_; 
v_before_509_ = lean_ctor_get(v_head_504_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_head_504_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_head_504_, 1);
lean_dec(v_unused_526_);
v___x_511_ = v_head_504_;
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_before_509_);
lean_dec(v_head_504_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 7);
lean_ctor_set(v___x_511_, 1, v___x_513_);
lean_ctor_set(v___x_511_, 0, v_x_502_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_x_502_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_524_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__3);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 7);
lean_ctor_set(v___x_507_, 1, v___x_516_);
lean_ctor_set(v___x_507_, 0, v___x_515_);
v___x_518_ = v___x_507_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_523_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = l_Lean_MessageData_ofSyntax(v_before_509_);
v___x_520_ = l_Lean_indentD(v___x_519_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v_x_502_ = v___x_521_;
v_x_503_ = v_tail_505_;
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
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__1));
v___x_532_ = l_Lean_MessageData_ofFormat(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(lean_object* v_msgData_533_, lean_object* v_macroStack_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_scopes_539_; lean_object* v___x_540_; lean_object* v_opts_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_537_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_538_ = lean_st_ref_get(v___y_535_);
v_scopes_539_ = lean_ctor_get(v___x_538_, 2);
lean_inc(v_scopes_539_);
lean_dec(v___x_538_);
v___x_540_ = l_List_head_x21___redArg(v___x_537_, v_scopes_539_);
lean_dec(v_scopes_539_);
v_opts_541_ = lean_ctor_get(v___x_540_, 1);
lean_inc_ref(v_opts_541_);
lean_dec(v___x_540_);
v___x_542_ = l_Lean_Elab_pp_macroStack;
v___x_543_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__7(v_opts_541_, v___x_542_);
lean_dec_ref(v_opts_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
lean_dec(v_macroStack_534_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_msgData_533_);
return v___x_544_;
}
else
{
if (lean_obj_tag(v_macroStack_534_) == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v_msgData_533_);
return v___x_545_;
}
else
{
lean_object* v_head_546_; lean_object* v_after_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_562_; 
v_head_546_ = lean_ctor_get(v_macroStack_534_, 0);
lean_inc(v_head_546_);
v_after_547_ = lean_ctor_get(v_head_546_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_head_546_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_head_546_, 0);
lean_dec(v_unused_563_);
v___x_549_ = v_head_546_;
v_isShared_550_ = v_isSharedCheck_562_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_after_547_);
lean_dec(v_head_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_562_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 7);
lean_ctor_set(v___x_549_, 1, v___x_551_);
lean_ctor_set(v___x_549_, 0, v_msgData_533_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_msgData_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_551_);
v___x_553_ = v_reuseFailAlloc_561_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_msgData_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_554_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___closed__2);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_MessageData_ofSyntax(v_after_547_);
v___x_557_ = l_Lean_indentD(v___x_556_);
v_msgData_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_558_, 0, v___x_555_);
lean_ctor_set(v_msgData_558_, 1, v___x_557_);
v___x_559_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5_spec__8(v_msgData_558_, v_macroStack_534_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_564_, lean_object* v_macroStack_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_msgData_564_, v_macroStack_565_, v___y_566_);
lean_dec(v___y_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Elab_Command_getRef___redArg(v___y_570_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_macroStack_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v_macroStack_575_ = lean_ctor_get(v___y_570_, 4);
v___x_576_ = l_Lean_Elab_getBetterRef(v_a_574_, v_macroStack_575_);
lean_dec(v_a_574_);
v___x_577_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msg_569_, v___y_571_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_577_);
lean_inc(v_macroStack_575_);
v___x_579_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_a_578_, v_macroStack_575_, v___y_571_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_576_);
lean_ctor_set(v___x_584_, 1, v_a_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 1);
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_msg_569_);
v_a_589_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_573_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_573_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg___boxed(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(lean_object* v_ref_602_, lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Elab_Command_getRef___redArg(v___y_604_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_fileName_609_; lean_object* v_fileMap_610_; lean_object* v_currRecDepth_611_; lean_object* v_cmdPos_612_; lean_object* v_macroStack_613_; lean_object* v_quotContext_x3f_614_; lean_object* v_currMacroScope_615_; lean_object* v_snap_x3f_616_; lean_object* v_cancelTk_x3f_617_; uint8_t v_suppressElabErrors_618_; uint8_t v_checkDeprecated_619_; lean_object* v_ref_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v_fileName_609_ = lean_ctor_get(v___y_604_, 0);
v_fileMap_610_ = lean_ctor_get(v___y_604_, 1);
v_currRecDepth_611_ = lean_ctor_get(v___y_604_, 2);
v_cmdPos_612_ = lean_ctor_get(v___y_604_, 3);
v_macroStack_613_ = lean_ctor_get(v___y_604_, 4);
v_quotContext_x3f_614_ = lean_ctor_get(v___y_604_, 5);
v_currMacroScope_615_ = lean_ctor_get(v___y_604_, 6);
v_snap_x3f_616_ = lean_ctor_get(v___y_604_, 8);
v_cancelTk_x3f_617_ = lean_ctor_get(v___y_604_, 9);
v_suppressElabErrors_618_ = lean_ctor_get_uint8(v___y_604_, sizeof(void*)*10);
v_checkDeprecated_619_ = lean_ctor_get_uint8(v___y_604_, sizeof(void*)*10 + 1);
v_ref_620_ = l_Lean_replaceRef(v_ref_602_, v_a_608_);
lean_dec(v_a_608_);
lean_inc(v_cancelTk_x3f_617_);
lean_inc(v_snap_x3f_616_);
lean_inc(v_currMacroScope_615_);
lean_inc(v_quotContext_x3f_614_);
lean_inc(v_macroStack_613_);
lean_inc(v_cmdPos_612_);
lean_inc(v_currRecDepth_611_);
lean_inc_ref(v_fileMap_610_);
lean_inc_ref(v_fileName_609_);
v___x_621_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_621_, 0, v_fileName_609_);
lean_ctor_set(v___x_621_, 1, v_fileMap_610_);
lean_ctor_set(v___x_621_, 2, v_currRecDepth_611_);
lean_ctor_set(v___x_621_, 3, v_cmdPos_612_);
lean_ctor_set(v___x_621_, 4, v_macroStack_613_);
lean_ctor_set(v___x_621_, 5, v_quotContext_x3f_614_);
lean_ctor_set(v___x_621_, 6, v_currMacroScope_615_);
lean_ctor_set(v___x_621_, 7, v_ref_620_);
lean_ctor_set(v___x_621_, 8, v_snap_x3f_616_);
lean_ctor_set(v___x_621_, 9, v_cancelTk_x3f_617_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*10, v_suppressElabErrors_618_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*10 + 1, v_checkDeprecated_619_);
v___x_622_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_603_, v___x_621_, v___y_605_);
lean_dec_ref_known(v___x_621_, 10);
return v___x_622_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_msg_603_);
v_a_623_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_607_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_607_);
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
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_ref_631_, lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_631_, v_msg_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v_ref_631_);
return v_res_636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__0));
v___x_639_ = l_Lean_stringToMessageData(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__2));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__4));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__6));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__8));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__10));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__12));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__14));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__16));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__18));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__21(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__20));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(lean_object* v_msg_670_, lean_object* v_declHint_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_env_676_; uint8_t v___x_677_; 
v___x_674_ = lean_box(0);
v___x_675_ = lean_st_ref_get(v___y_672_);
v_env_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc_ref(v_env_676_);
lean_dec(v___x_675_);
v___x_677_ = l_Lean_Name_isAnonymous(v_declHint_671_);
if (v___x_677_ == 0)
{
uint8_t v_isExporting_678_; 
v_isExporting_678_ = lean_ctor_get_uint8(v_env_676_, sizeof(void*)*13);
if (v_isExporting_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_671_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_msg_670_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
lean_inc_ref(v_env_676_);
v___x_680_ = l_Lean_Environment_setExporting(v_env_676_, v___x_677_);
lean_inc(v_declHint_671_);
lean_inc_ref(v___x_680_);
v___x_681_ = l_Lean_Environment_contains(v___x_680_, v_declHint_671_, v_isExporting_678_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v___x_680_);
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_671_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_msg_670_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_c_688_; lean_object* v___x_689_; 
v___x_683_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__2);
v___x_684_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg___closed__5);
v___x_685_ = l_Lean_Options_empty;
lean_inc_ref(v___x_680_);
v___x_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_686_, 0, v___x_680_);
lean_ctor_set(v___x_686_, 1, v___x_683_);
lean_ctor_set(v___x_686_, 2, v___x_684_);
lean_ctor_set(v___x_686_, 3, v___x_685_);
lean_inc(v_declHint_671_);
v___x_687_ = l_Lean_MessageData_ofConstName(v_declHint_671_, v___x_677_);
v_c_688_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_688_, 0, v___x_686_);
lean_ctor_set(v_c_688_, 1, v___x_687_);
v___x_689_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_680_, v_declHint_671_);
lean_dec_ref(v___x_680_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_671_);
v___x_690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_c_688_);
v___x_692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__3);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_MessageData_note(v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v_msg_670_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_val_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_750_; 
v_val_697_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_750_ == 0)
{
v___x_699_ = v___x_689_;
v_isShared_700_ = v_isSharedCheck_750_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_val_697_);
lean_dec(v___x_689_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_750_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v_modules_702_; lean_object* v_moduleNames_703_; lean_object* v_mod_704_; uint8_t v___x_719_; 
v___x_701_ = l_Lean_Environment_header(v_env_676_);
lean_dec_ref(v_env_676_);
v_modules_702_ = lean_ctor_get(v___x_701_, 3);
lean_inc_ref(v_modules_702_);
v_moduleNames_703_ = lean_ctor_get(v___x_701_, 4);
lean_inc_ref(v_moduleNames_703_);
lean_dec_ref(v___x_701_);
v_mod_704_ = lean_array_get(v___x_674_, v_moduleNames_703_, v_val_697_);
lean_dec_ref(v_moduleNames_703_);
v___x_719_ = l_Lean_isPrivateName(v_declHint_671_);
lean_dec(v_declHint_671_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_get_size(v_modules_702_);
v___x_721_ = lean_nat_dec_lt(v_val_697_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_modules_702_);
lean_dec(v_val_697_);
goto v___jp_705_;
}
else
{
lean_object* v___x_722_; lean_object* v_toImport_723_; uint8_t v_isExported_724_; 
v___x_722_ = lean_array_fget(v_modules_702_, v_val_697_);
lean_dec(v_val_697_);
lean_dec_ref(v_modules_702_);
v_toImport_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_toImport_723_);
lean_dec(v___x_722_);
v_isExported_724_ = lean_ctor_get_uint8(v_toImport_723_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_723_);
if (v_isExported_724_ == 0)
{
goto v___jp_705_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_del_object(v___x_699_);
v___x_725_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__11);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_c_688_);
v___x_727_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__13);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_MessageData_ofName(v_mod_704_);
lean_inc_ref(v___x_729_);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__15);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_729_);
v___x_734_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__17);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_MessageData_note(v___x_735_);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v_msg_670_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v_modules_702_);
lean_del_object(v___x_699_);
lean_dec(v_val_697_);
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__1);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v_c_688_);
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__19);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_ofName(v_mod_704_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__21);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_MessageData_note(v___x_746_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v_msg_670_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
v___jp_705_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__5);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_c_688_);
v___x_708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__7);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_MessageData_ofName(v_mod_704_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___closed__9);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_MessageData_note(v___x_713_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v_msg_670_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
lean_ctor_set(v___x_699_, 0, v___x_715_);
v___x_717_ = v___x_699_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_751_; 
lean_dec_ref(v_env_676_);
lean_dec(v_declHint_671_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_msg_670_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg___boxed(lean_object* v_msg_752_, lean_object* v_declHint_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_752_, v_declHint_753_, v___y_754_);
lean_dec(v___y_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(lean_object* v_msg_757_, lean_object* v_declHint_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_772_; 
v___x_762_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_757_, v_declHint_758_, v___y_760_);
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_772_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_772_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = l_Lean_unknownIdentifierMessageTag;
v___x_768_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10___boxed(lean_object* v_msg_773_, lean_object* v_declHint_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(v_msg_773_, v_declHint_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(lean_object* v_ref_779_, lean_object* v_msg_780_, lean_object* v_declHint_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_787_; 
v___x_785_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10(v_msg_780_, v_declHint_781_, v___y_782_, v___y_783_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref(v___x_785_);
v___x_787_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_779_, v_a_786_, v___y_782_, v___y_783_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_ref_788_, lean_object* v_msg_789_, lean_object* v_declHint_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_788_, v_msg_789_, v_declHint_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v_ref_788_);
return v_res_794_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__0));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__70));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(lean_object* v_ref_800_, lean_object* v_constName_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_805_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__1);
v___x_806_ = 0;
lean_inc(v_constName_801_);
v___x_807_ = l_Lean_MessageData_ofConstName(v_constName_801_, v___x_806_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_805_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___closed__2);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_800_, v___x_810_, v_constName_801_, v___y_802_, v___y_803_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_ref_812_, lean_object* v_constName_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_ref_812_, v_constName_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v_ref_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(lean_object* v_constName_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_Command_getRef___redArg(v___y_819_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_a_823_, v_constName_818_, v___y_819_, v___y_820_);
lean_dec(v_a_823_);
return v___x_824_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_constName_818_);
v_a_825_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_822_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_822_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg___boxed(lean_object* v_constName_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(lean_object* v_constName_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_env_843_; uint8_t v___x_844_; lean_object* v___x_845_; 
v___x_842_ = lean_st_ref_get(v___y_840_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v___x_844_ = 0;
lean_inc(v_constName_838_);
v___x_845_ = l_Lean_Environment_find_x3f(v_env_843_, v_constName_838_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_838_, v___y_839_, v___y_840_);
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_constName_838_);
v_val_847_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 0);
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_val_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2___boxed(lean_object* v_constName_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(v_constName_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_859_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__1));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(lean_object* v_as_864_, size_t v_sz_865_, size_t v_i_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
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
lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___x_885_; 
v___f_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__0));
v___x_874_ = lean_box(0);
v_a_875_ = lean_array_uget_borrowed(v_as_864_, v_i_866_);
lean_inc_n(v_a_875_, 2);
v___f_876_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___boxed), 4, 1);
lean_closure_set(v___f_876_, 0, v_a_875_);
v___f_877_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__2___boxed), 4, 1);
lean_closure_set(v___f_877_, 0, v___f_876_);
v___x_885_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2(v_a_875_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_ConstantInfo_levelParams(v_a_886_);
lean_dec(v_a_886_);
v___x_888_ = l_List_isEmpty___redArg(v___x_887_);
lean_dec(v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_inc(v_a_875_);
v___x_889_ = l_Lean_MessageData_ofConstName(v_a_875_, v___x_888_);
v___x_890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___closed__2);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v___x_891_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v___y_879_ = v___y_868_;
v___y_880_ = v___y_869_;
goto v___jp_878_;
}
else
{
lean_dec_ref(v___f_877_);
return v___x_892_;
}
}
else
{
v___y_879_ = v___y_868_;
v___y_880_ = v___y_869_;
goto v___jp_878_;
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___f_877_);
v_a_893_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_885_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_885_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
v___jp_878_:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Elab_Command_withScope___redArg(v___f_873_, v___f_877_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
size_t v___x_882_; size_t v___x_883_; 
lean_dec_ref_known(v___x_881_, 1);
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_866_, v___x_882_);
v_i_866_ = v___x_883_;
v_b_867_ = v___x_874_;
goto _start;
}
else
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___boxed(lean_object* v_as_901_, lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_sz_boxed_908_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_909_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(v_as_901_, v_sz_boxed_908_, v_i_boxed_909_, v_b_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec_ref(v_as_901_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(lean_object* v_declNames_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; size_t v_sz_916_; size_t v___x_917_; lean_object* v___x_918_; 
v___x_915_ = lean_box(0);
v_sz_916_ = lean_array_size(v_declNames_911_);
v___x_917_ = ((size_t)0ULL);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4(v_declNames_911_, v_sz_916_, v___x_917_, v___x_915_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_927_; 
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v___x_918_, 0);
lean_dec(v_unused_928_);
v___x_920_ = v___x_918_;
v_isShared_921_ = v_isSharedCheck_927_;
goto v_resetjp_919_;
}
else
{
lean_dec(v___x_918_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_927_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_922_ = 1;
v___x_923_ = lean_box(v___x_922_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_923_);
v___x_925_ = v___x_920_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_918_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_918_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance___boxed(lean_object* v_declNames_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance(v_declNames_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec_ref(v_declNames_937_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(lean_object* v_msgData_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___redArg(v_msgData_942_, v___y_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4___boxed(lean_object* v_msgData_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__4(v_msgData_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(lean_object* v_00_u03b1_952_, lean_object* v_msg_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___redArg(v_msg_953_, v___y_954_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3___boxed(lean_object* v_00_u03b1_958_, lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3(v_00_u03b1_958_, v_msg_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(lean_object* v_00_u03b1_964_, lean_object* v_constName_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___redArg(v_constName_965_, v___y_966_, v___y_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2___boxed(lean_object* v_00_u03b1_970_, lean_object* v_constName_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2(v_00_u03b1_970_, v_constName_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(lean_object* v_msgData_976_, lean_object* v_macroStack_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___redArg(v_msgData_976_, v_macroStack_977_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5___boxed(lean_object* v_msgData_982_, lean_object* v_macroStack_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__3_spec__5(v_msgData_982_, v_macroStack_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_988_, lean_object* v_ref_989_, lean_object* v_constName_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___redArg(v_ref_989_, v_constName_990_, v___y_991_, v___y_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_995_, lean_object* v_ref_996_, lean_object* v_constName_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3(v_00_u03b1_995_, v_ref_996_, v_constName_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v_ref_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(lean_object* v_00_u03b1_1002_, lean_object* v_ref_1003_, lean_object* v_msg_1004_, lean_object* v_declHint_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___redArg(v_ref_1003_, v_msg_1004_, v_declHint_1005_, v___y_1006_, v___y_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_ref_1011_, lean_object* v_msg_1012_, lean_object* v_declHint_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7(v_00_u03b1_1010_, v_ref_1011_, v_msg_1012_, v_declHint_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v_ref_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(lean_object* v_msg_1018_, lean_object* v_declHint_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___redArg(v_msg_1018_, v_declHint_1019_, v___y_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12___boxed(lean_object* v_msg_1024_, lean_object* v_declHint_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__10_spec__12(v_msg_1024_, v_declHint_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(lean_object* v_00_u03b1_1030_, lean_object* v_ref_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___redArg(v_ref_1031_, v_msg_1032_, v___y_1033_, v___y_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b1_1037_, lean_object* v_ref_1038_, lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__2_spec__2_spec__3_spec__7_spec__11(v_00_u03b1_1037_, v_ref_1038_, v_msg_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v_ref_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_deriveTypeNameInstance_spec__4___lam__1___closed__48));
v___x_1047_ = ((lean_object*)(l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_));
v___x_1048_ = l_Lean_Elab_registerDerivingHandler(v___x_1046_, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2____boxed(lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Elab_Deriving_TypeName_0__Lean_Elab_initFn_00___x40_Lean_Elab_Deriving_TypeName_4279947348____hygCtx___hyg_2_();
return v_res_1050_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
