// Lean compiler output
// Module: Lean.Elab.Deriving.Nonempty
// Imports: public import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__14_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__16_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Classical.ofNonempty"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofNonempty"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(197, 41, 144, 91, 215, 43, 73, 12)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 79, 35, 19, 21, 38, 89, 10)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "variable"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 93, 226, 106, 76, 14, 69, 165)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__31_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__33_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__35_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__37_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__39_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__40_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__42_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__41_value),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__44_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__38_value),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__45_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__36_value),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__46_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__34_value),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__47_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__32_value),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__48_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__51_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__54_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "constructor"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57_value),LEAN_SCALAR_PTR_LITERAL(144, 188, 57, 91, 27, 124, 155, 13)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__65 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__65_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__65_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v_b_4_, lean_object* v_c_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_k_1_, v_b_4_, v_c_5_, v___y_2_, v___y_3_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0___boxed(lean_object* v_k_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v_b_15_, lean_object* v_c_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0(v_k_12_, v___y_13_, v___y_14_, v_b_15_, v_c_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(lean_object* v_type_23_, lean_object* v_k_24_, uint8_t v_cleanupAnnotations_25_, uint8_t v_whnfType_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_34_, 0, v_k_24_);
lean_closure_set(v___f_34_, 1, v___y_27_);
lean_closure_set(v___f_34_, 2, v___y_28_);
v___x_35_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_23_, v___f_34_, v_cleanupAnnotations_25_, v_whnfType_26_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg___boxed(lean_object* v_type_44_, lean_object* v_k_45_, lean_object* v_cleanupAnnotations_46_, lean_object* v_whnfType_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; uint8_t v_whnfType_boxed_56_; lean_object* v_res_57_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_46_);
v_whnfType_boxed_56_ = lean_unbox(v_whnfType_47_);
v_res_57_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_44_, v_k_45_, v_cleanupAnnotations_boxed_55_, v_whnfType_boxed_56_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6(lean_object* v_00_u03b1_58_, lean_object* v_type_59_, lean_object* v_k_60_, uint8_t v_cleanupAnnotations_61_, uint8_t v_whnfType_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_59_, v_k_60_, v_cleanupAnnotations_61_, v_whnfType_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___boxed(lean_object* v_00_u03b1_71_, lean_object* v_type_72_, lean_object* v_k_73_, lean_object* v_cleanupAnnotations_74_, lean_object* v_whnfType_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_83_; uint8_t v_whnfType_boxed_84_; lean_object* v_res_85_; 
v_cleanupAnnotations_boxed_83_ = lean_unbox(v_cleanupAnnotations_74_);
v_whnfType_boxed_84_ = lean_unbox(v_whnfType_75_);
v_res_85_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6(v_00_u03b1_71_, v_type_72_, v_k_73_, v_cleanupAnnotations_boxed_83_, v_whnfType_boxed_84_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(lean_object* v___x_108_, size_t v_sz_109_, size_t v_i_110_, lean_object* v_bs_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = lean_usize_dec_lt(v_i_110_, v_sz_109_);
if (v___x_112_ == 0)
{
lean_dec(v___x_108_);
return v_bs_111_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_v_116_; lean_object* v___x_117_; lean_object* v_bs_x27_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4));
v___x_114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6));
v___x_115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8));
v_v_116_ = lean_array_uget(v_bs_111_, v_i_110_);
v___x_117_ = lean_unsigned_to_nat(0u);
v_bs_x27_118_ = lean_array_uset(v_bs_111_, v_i_110_, v___x_117_);
v___x_119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__10));
v___x_120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__11));
lean_inc_n(v___x_108_, 5);
v___x_121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_108_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_Syntax_node1(v___x_108_, v___x_114_, v_v_116_);
v___x_123_ = l_Lean_Syntax_node1(v___x_108_, v___x_113_, v___x_122_);
v___x_124_ = l_Lean_Syntax_node1(v___x_108_, v___x_115_, v___x_123_);
v___x_125_ = l_Lean_Syntax_node2(v___x_108_, v___x_119_, v___x_121_, v___x_124_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_110_, v___x_126_);
v___x_128_ = lean_array_uset(v_bs_x27_118_, v_i_110_, v___x_125_);
v_i_110_ = v___x_127_;
v_bs_111_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___boxed(lean_object* v___x_130_, lean_object* v_sz_131_, lean_object* v_i_132_, lean_object* v_bs_133_){
_start:
{
size_t v_sz_boxed_134_; size_t v_i_boxed_135_; lean_object* v_res_136_; 
v_sz_boxed_134_ = lean_unbox_usize(v_sz_131_);
lean_dec(v_sz_131_);
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(v___x_130_, v_sz_boxed_134_, v_i_boxed_135_, v_bs_133_);
return v_res_136_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Array_mkArray0(lean_box(0));
return v___x_138_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__11));
v___x_162_ = l_String_toRawSubstring_x27(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(lean_object* v_as_177_, size_t v_sz_178_, size_t v_i_179_, lean_object* v_b_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_a_187_; uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_b_180_);
return v___x_192_;
}
else
{
lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_a_193_ = lean_array_uget_borrowed(v_as_177_, v_i_179_);
v___x_194_ = l_Lean_Expr_fvarId_x21(v_a_193_);
v___x_195_ = l_Lean_FVarId_getUserName___redArg(v___x_194_, v___y_181_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_195_, 1);
v___x_197_ = l_Lean_Name_eraseMacroScopes(v_a_196_);
lean_dec(v_a_196_);
v___x_198_ = l_Lean_Core_mkFreshUserName(v___x_197_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_toCold_200_; lean_object* v_ref_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v_toCold_200_ = lean_ctor_get(v___y_183_, 0);
v_ref_201_ = lean_ctor_get(v___y_183_, 2);
v___x_202_ = l_Lean_mkIdent(v_a_199_);
v___x_203_ = 0;
v___x_204_ = l_Lean_SourceInfo_fromRef(v_ref_201_, v___x_203_);
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0));
lean_inc_n(v___x_204_, 2);
v___x_206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6));
lean_inc(v___x_202_);
v___x_208_ = l_Lean_Syntax_node1(v___x_204_, v___x_207_, v___x_202_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v_a_193_);
v___x_209_ = lean_infer_type(v_a_193_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
v___x_211_ = lean_whnf(v_a_210_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_262_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v_fst_213_ = lean_ctor_get(v_b_180_, 0);
v_snd_214_ = lean_ctor_get(v_b_180_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_b_180_);
if (v_isSharedCheck_262_ == 0)
{
v___x_216_ = v_b_180_;
v_isShared_217_ = v_isSharedCheck_262_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_snd_214_);
lean_inc(v_fst_213_);
lean_dec(v_b_180_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_262_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_218_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1);
lean_inc_n(v___x_204_, 3);
v___x_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_219_, 0, v___x_204_);
lean_ctor_set(v___x_219_, 1, v___x_207_);
lean_ctor_set(v___x_219_, 2, v___x_218_);
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3));
v___x_221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_204_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_array_push(v_fst_213_, v___x_202_);
v___x_223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5));
lean_inc_ref(v___x_219_);
lean_inc(v___x_208_);
v___x_224_ = l_Lean_Syntax_node4(v___x_204_, v___x_223_, v___x_206_, v___x_208_, v___x_219_, v___x_221_);
v___x_225_ = lean_array_push(v_snd_214_, v___x_224_);
if (lean_obj_tag(v_a_212_) == 3)
{
lean_object* v_u_226_; lean_object* v___x_227_; 
v_u_226_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_u_226_);
lean_dec_ref_known(v_a_212_, 1);
v___x_227_ = l_Lean_Meta_decLevel_x3f(v_u_226_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
if (lean_obj_tag(v_a_228_) == 1)
{
lean_object* v_quotContext_229_; lean_object* v_currMacroScope_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec_ref_known(v_a_228_, 1);
v_quotContext_229_ = lean_ctor_get(v_toCold_200_, 8);
v_currMacroScope_230_ = lean_ctor_get(v_toCold_200_, 9);
v___x_231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7));
v___x_232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8));
lean_inc_n(v___x_204_, 4);
v___x_233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_204_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10));
v___x_235_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12);
v___x_236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13));
lean_inc(v_currMacroScope_230_);
lean_inc(v_quotContext_229_);
v___x_237_ = l_Lean_addMacroScope(v_quotContext_229_, v___x_236_, v_currMacroScope_230_);
v___x_238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17));
v___x_239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_239_, 0, v___x_204_);
lean_ctor_set(v___x_239_, 1, v___x_235_);
lean_ctor_set(v___x_239_, 2, v___x_237_);
lean_ctor_set(v___x_239_, 3, v___x_238_);
v___x_240_ = l_Lean_Syntax_node2(v___x_204_, v___x_234_, v___x_239_, v___x_208_);
v___x_241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18));
v___x_242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_204_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_Syntax_node4(v___x_204_, v___x_231_, v___x_233_, v___x_219_, v___x_240_, v___x_242_);
v___x_244_ = lean_array_push(v___x_225_, v___x_243_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_244_);
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_246_ = v___x_216_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_a_187_ = v___x_246_;
goto v___jp_186_;
}
}
else
{
lean_object* v___x_249_; 
lean_dec(v_a_228_);
lean_dec_ref_known(v___x_219_, 3);
lean_dec(v___x_208_);
lean_dec(v___x_204_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_225_);
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_249_ = v___x_216_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_225_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
v_a_187_ = v___x_249_;
goto v___jp_186_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v___x_225_);
lean_dec_ref(v___x_222_);
lean_dec_ref_known(v___x_219_, 3);
lean_del_object(v___x_216_);
lean_dec(v___x_208_);
lean_dec(v___x_204_);
v_a_251_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_227_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_227_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec_ref_known(v___x_219_, 3);
lean_dec(v_a_212_);
lean_dec(v___x_208_);
lean_dec(v___x_204_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_225_);
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_260_ = v___x_216_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_225_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v_a_187_ = v___x_260_;
goto v___jp_186_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v___x_208_);
lean_dec_ref_known(v___x_206_, 2);
lean_dec(v___x_204_);
lean_dec(v___x_202_);
lean_dec_ref(v_b_180_);
v_a_263_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_211_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_211_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec(v___x_208_);
lean_dec_ref_known(v___x_206_, 2);
lean_dec(v___x_204_);
lean_dec(v___x_202_);
lean_dec_ref(v_b_180_);
v_a_271_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_209_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_209_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_b_180_);
v_a_279_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_198_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_198_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_b_180_);
v_a_287_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_195_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_195_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
v___jp_186_:
{
size_t v___x_188_; size_t v___x_189_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_179_, v___x_188_);
v_i_179_ = v___x_189_;
v_b_180_ = v_a_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___boxed(lean_object* v_as_295_, lean_object* v_sz_296_, lean_object* v_i_297_, lean_object* v_b_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
size_t v_sz_boxed_304_; size_t v_i_boxed_305_; lean_object* v_res_306_; 
v_sz_boxed_304_ = lean_unbox_usize(v_sz_296_);
lean_dec(v_sz_296_);
v_i_boxed_305_ = lean_unbox_usize(v_i_297_);
lean_dec(v_i_297_);
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_as_295_, v_sz_boxed_304_, v_i_boxed_305_, v_b_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec_ref(v_as_295_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(size_t v_sz_307_, size_t v_i_308_, lean_object* v_bs_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_310_ == 0)
{
return v_bs_309_;
}
else
{
lean_object* v_v_311_; lean_object* v___x_312_; lean_object* v_bs_x27_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v_v_311_ = lean_array_uget(v_bs_309_, v_i_308_);
v___x_312_ = lean_unsigned_to_nat(0u);
v_bs_x27_313_ = lean_array_uset(v_bs_309_, v_i_308_, v___x_312_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_308_, v___x_314_);
v___x_316_ = lean_array_uset(v_bs_x27_313_, v_i_308_, v_v_311_);
v_i_308_ = v___x_315_;
v_bs_309_ = v___x_316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4___boxed(lean_object* v_sz_318_, lean_object* v_i_319_, lean_object* v_bs_320_){
_start:
{
size_t v_sz_boxed_321_; size_t v_i_boxed_322_; lean_object* v_res_323_; 
v_sz_boxed_321_ = lean_unbox_usize(v_sz_318_);
lean_dec(v_sz_318_);
v_i_boxed_322_ = lean_unbox_usize(v_i_319_);
lean_dec(v_i_319_);
v_res_323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(v_sz_boxed_321_, v_i_boxed_322_, v_bs_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(size_t v_sz_324_, size_t v_i_325_, lean_object* v_bs_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_327_ == 0)
{
return v_bs_326_;
}
else
{
lean_object* v_v_328_; lean_object* v___x_329_; lean_object* v_bs_x27_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v_v_328_ = lean_array_uget(v_bs_326_, v_i_325_);
v___x_329_ = lean_unsigned_to_nat(0u);
v_bs_x27_330_ = lean_array_uset(v_bs_326_, v_i_325_, v___x_329_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_325_, v___x_331_);
v___x_333_ = lean_array_uset(v_bs_x27_330_, v_i_325_, v_v_328_);
v_i_325_ = v___x_332_;
v_bs_326_ = v___x_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3___boxed(lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_bs_337_){
_start:
{
size_t v_sz_boxed_338_; size_t v_i_boxed_339_; lean_object* v_res_340_; 
v_sz_boxed_338_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_339_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(v_sz_boxed_338_, v_i_boxed_339_, v_bs_337_);
return v_res_340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10));
v___x_369_ = l_String_toRawSubstring_x27(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(size_t v_sz_381_, size_t v_i_382_, lean_object* v_bs_383_, lean_object* v___y_384_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_bs_383_);
return v___x_387_;
}
else
{
lean_object* v_toCold_388_; lean_object* v_ref_389_; lean_object* v_quotContext_390_; lean_object* v_currMacroScope_391_; lean_object* v_v_392_; lean_object* v___x_393_; lean_object* v_bs_x27_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v_toCold_388_ = lean_ctor_get(v___y_384_, 0);
v_ref_389_ = lean_ctor_get(v___y_384_, 2);
v_quotContext_390_ = lean_ctor_get(v_toCold_388_, 8);
v_currMacroScope_391_ = lean_ctor_get(v_toCold_388_, 9);
v_v_392_ = lean_array_uget(v_bs_383_, v_i_382_);
v___x_393_ = lean_unsigned_to_nat(0u);
v_bs_x27_394_ = lean_array_uset(v_bs_383_, v_i_382_, v___x_393_);
v___x_395_ = 0;
v___x_396_ = l_Lean_SourceInfo_fromRef(v_ref_389_, v___x_395_);
v___x_397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1));
v___x_398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2));
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3));
lean_inc_n(v___x_396_, 8);
v___x_400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_396_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
v___x_401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5));
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6));
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_396_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_mkCIdent(v_v_392_);
v___x_405_ = l_Lean_Syntax_node2(v___x_396_, v___x_401_, v___x_403_, v___x_404_);
v___x_406_ = l_Lean_Syntax_node2(v___x_396_, v___x_399_, v___x_400_, v___x_405_);
v___x_407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7));
v___x_408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_396_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8));
v___x_410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9));
v___x_411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_396_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
v___x_412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11);
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14));
lean_inc(v_currMacroScope_391_);
lean_inc(v_quotContext_390_);
v___x_414_ = l_Lean_addMacroScope(v_quotContext_390_, v___x_413_, v_currMacroScope_391_);
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16));
v___x_416_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_416_, 0, v___x_396_);
lean_ctor_set(v___x_416_, 1, v___x_412_);
lean_ctor_set(v___x_416_, 2, v___x_414_);
lean_ctor_set(v___x_416_, 3, v___x_415_);
v___x_417_ = l_Lean_Syntax_node2(v___x_396_, v___x_410_, v___x_411_, v___x_416_);
v___x_418_ = l_Lean_Syntax_node3(v___x_396_, v___x_397_, v___x_406_, v___x_408_, v___x_417_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_382_, v___x_419_);
v___x_421_ = lean_array_uset(v_bs_x27_394_, v_i_382_, v___x_418_);
v_i_382_ = v___x_420_;
v_bs_383_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___boxed(lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_bs_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
size_t v_sz_boxed_428_; size_t v_i_boxed_429_; lean_object* v_res_430_; 
v_sz_boxed_428_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_429_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_boxed_428_, v_i_boxed_429_, v_bs_425_, v___y_426_);
lean_dec_ref(v___y_426_);
return v_res_430_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27));
v___x_503_ = l_String_toRawSubstring_x27(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(lean_object* v_ctors_600_, lean_object* v_declName_601_, lean_object* v_paramsIndices_602_, lean_object* v_x_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; size_t v_sz_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1));
v_sz_612_ = lean_array_size(v_paramsIndices_602_);
v___x_613_ = ((size_t)0ULL);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_paramsIndices_602_, v_sz_612_, v___x_613_, v___x_611_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; size_t v_sz_617_; lean_object* v___x_618_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = lean_array_mk(v_ctors_600_);
v_sz_617_ = lean_array_size(v___x_616_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_617_, v___x_613_, v___x_616_, v___y_608_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_toCold_619_; lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_735_; 
v_toCold_619_ = lean_ctor_get(v___y_608_, 0);
v_a_620_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_735_ == 0)
{
v___x_622_ = v___x_618_;
v_isShared_623_ = v_isSharedCheck_735_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_618_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_735_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_734_; 
v_fst_624_ = lean_ctor_get(v_a_615_, 0);
v_snd_625_ = lean_ctor_get(v_a_615_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_615_);
if (v_isSharedCheck_734_ == 0)
{
v___x_627_ = v_a_615_;
v_isShared_628_ = v_isSharedCheck_734_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_625_);
lean_inc(v_fst_624_);
lean_dec(v_a_615_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_734_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_ref_629_; lean_object* v_quotContext_630_; lean_object* v_currMacroScope_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v_ref_629_ = lean_ctor_get(v___y_608_, 2);
v_quotContext_630_ = lean_ctor_get(v_toCold_619_, 8);
v_currMacroScope_631_ = lean_ctor_get(v_toCold_619_, 9);
v___x_632_ = 0;
v___x_633_ = l_Lean_SourceInfo_fromRef(v_ref_629_, v___x_632_);
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3));
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4));
v___x_636_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5));
v___x_637_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6));
lean_inc(v___x_633_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 2);
lean_ctor_set(v___x_627_, 1, v___x_636_);
lean_ctor_set(v___x_627_, 0, v___x_633_);
v___x_639_ = v___x_627_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_636_);
v___x_639_ = v_reuseFailAlloc_733_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; size_t v_sz_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; size_t v_sz_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; size_t v_sz_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6));
v___x_641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1);
v_sz_642_ = lean_array_size(v_snd_625_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(v_sz_642_, v___x_613_, v_snd_625_);
v___x_644_ = l_Array_append___redArg(v___x_641_, v___x_643_);
lean_dec_ref(v___x_643_);
lean_inc_n(v___x_633_, 41);
v___x_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_645_, 0, v___x_633_);
lean_ctor_set(v___x_645_, 1, v___x_640_);
lean_ctor_set(v___x_645_, 2, v___x_644_);
v___x_646_ = l_Lean_Syntax_node2(v___x_633_, v___x_637_, v___x_639_, v___x_645_);
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_633_);
lean_ctor_set(v___x_647_, 1, v___x_634_);
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8));
v___x_649_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10));
v___x_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_650_, 0, v___x_633_);
lean_ctor_set(v___x_650_, 1, v___x_640_);
lean_ctor_set(v___x_650_, 2, v___x_641_);
lean_inc_ref_n(v___x_650_, 14);
v___x_651_ = l_Lean_Syntax_node7(v___x_633_, v___x_649_, v___x_650_, v___x_650_, v___x_650_, v___x_650_, v___x_650_, v___x_650_, v___x_650_);
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11));
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12));
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14));
v___x_655_ = l_Lean_Syntax_node1(v___x_633_, v___x_654_, v___x_650_);
v___x_656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_633_);
lean_ctor_set(v___x_656_, 1, v___x_652_);
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16));
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18));
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19));
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_633_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10));
v___x_662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12);
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13));
lean_inc_n(v_currMacroScope_631_, 2);
lean_inc_n(v_quotContext_630_, 2);
v___x_664_ = l_Lean_addMacroScope(v_quotContext_630_, v___x_663_, v_currMacroScope_631_);
v___x_665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17));
v___x_666_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_666_, 0, v___x_633_);
lean_ctor_set(v___x_666_, 1, v___x_662_);
lean_ctor_set(v___x_666_, 2, v___x_664_);
lean_ctor_set(v___x_666_, 3, v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21));
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23));
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24));
v___x_670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_633_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26));
v___x_672_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28, &l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28_once, _init_l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28);
v___x_673_ = lean_box(0);
v___x_674_ = l_Lean_addMacroScope(v_quotContext_630_, v___x_673_, v_currMacroScope_631_);
v___x_675_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49));
v___x_676_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_676_, 0, v___x_633_);
lean_ctor_set(v___x_676_, 1, v___x_672_);
lean_ctor_set(v___x_676_, 2, v___x_674_);
lean_ctor_set(v___x_676_, 3, v___x_675_);
v___x_677_ = l_Lean_Syntax_node1(v___x_633_, v___x_671_, v___x_676_);
v___x_678_ = l_Lean_Syntax_node2(v___x_633_, v___x_668_, v___x_670_, v___x_677_);
v___x_679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5));
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6));
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_633_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_mkCIdent(v_declName_601_);
v___x_683_ = l_Lean_Syntax_node2(v___x_633_, v___x_679_, v___x_681_, v___x_682_);
v_sz_684_ = lean_array_size(v_fst_624_);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(v_sz_684_, v___x_613_, v_fst_624_);
v___x_686_ = l_Array_append___redArg(v___x_641_, v___x_685_);
lean_dec_ref(v___x_685_);
v___x_687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_633_);
lean_ctor_set(v___x_687_, 1, v___x_640_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
v___x_688_ = l_Lean_Syntax_node2(v___x_633_, v___x_661_, v___x_683_, v___x_687_);
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50));
v___x_690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_633_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_Syntax_node3(v___x_633_, v___x_667_, v___x_678_, v___x_688_, v___x_690_);
v___x_692_ = l_Lean_Syntax_node1(v___x_633_, v___x_640_, v___x_691_);
v___x_693_ = l_Lean_Syntax_node2(v___x_633_, v___x_661_, v___x_666_, v___x_692_);
v___x_694_ = l_Lean_Syntax_node2(v___x_633_, v___x_658_, v___x_660_, v___x_693_);
v___x_695_ = l_Lean_Syntax_node2(v___x_633_, v___x_657_, v___x_650_, v___x_694_);
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52));
v___x_697_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53));
v___x_698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_633_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55));
v___x_700_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56));
v___x_701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_633_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8));
v___x_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4));
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57));
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58));
v___x_706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_633_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60));
v___x_708_ = l_Lean_Syntax_node1(v___x_633_, v___x_707_, v___x_650_);
v___x_709_ = l_Lean_Syntax_node2(v___x_633_, v___x_705_, v___x_706_, v___x_708_);
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61));
v___x_711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_633_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62));
v___x_713_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_633_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
v_sz_715_ = lean_array_size(v_a_620_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(v___x_633_, v_sz_715_, v___x_613_, v_a_620_);
v___x_717_ = l_Array_append___redArg(v___x_641_, v___x_716_);
lean_dec_ref(v___x_716_);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v___x_633_);
lean_ctor_set(v___x_718_, 1, v___x_640_);
lean_ctor_set(v___x_718_, 2, v___x_717_);
v___x_719_ = l_Lean_Syntax_node2(v___x_633_, v___x_713_, v___x_714_, v___x_718_);
v___x_720_ = l_Lean_Syntax_node3(v___x_633_, v___x_640_, v___x_709_, v___x_711_, v___x_719_);
v___x_721_ = l_Lean_Syntax_node1(v___x_633_, v___x_703_, v___x_720_);
v___x_722_ = l_Lean_Syntax_node1(v___x_633_, v___x_702_, v___x_721_);
v___x_723_ = l_Lean_Syntax_node2(v___x_633_, v___x_699_, v___x_701_, v___x_722_);
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__66));
v___x_725_ = l_Lean_Syntax_node2(v___x_633_, v___x_724_, v___x_650_, v___x_650_);
v___x_726_ = l_Lean_Syntax_node4(v___x_633_, v___x_696_, v___x_698_, v___x_723_, v___x_725_, v___x_650_);
v___x_727_ = l_Lean_Syntax_node6(v___x_633_, v___x_653_, v___x_655_, v___x_656_, v___x_650_, v___x_650_, v___x_695_, v___x_726_);
v___x_728_ = l_Lean_Syntax_node2(v___x_633_, v___x_648_, v___x_651_, v___x_727_);
v___x_729_ = l_Lean_Syntax_node3(v___x_633_, v___x_635_, v___x_646_, v___x_647_, v___x_728_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_729_);
v___x_731_ = v___x_622_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_a_615_);
lean_dec(v_declName_601_);
v_a_736_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_618_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_618_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_declName_601_);
lean_dec(v_ctors_600_);
v_a_744_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_614_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_614_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed(lean_object* v_ctors_752_, lean_object* v_declName_753_, lean_object* v_paramsIndices_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(v_ctors_752_, v_declName_753_, v_paramsIndices_754_, v_x_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec_ref(v_x_755_);
lean_dec_ref(v_paramsIndices_754_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(lean_object* v_msgData_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_env_771_; lean_object* v___x_772_; lean_object* v_toCold_773_; lean_object* v_mctx_774_; lean_object* v_lctx_775_; lean_object* v_options_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_770_ = lean_st_ref_get(v___y_768_);
v_env_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_ref(v_env_771_);
lean_dec(v___x_770_);
v___x_772_ = lean_st_ref_get(v___y_766_);
v_toCold_773_ = lean_ctor_get(v___y_767_, 0);
v_mctx_774_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_mctx_774_);
lean_dec(v___x_772_);
v_lctx_775_ = lean_ctor_get(v___y_765_, 2);
v_options_776_ = lean_ctor_get(v_toCold_773_, 2);
lean_inc_ref(v_options_776_);
lean_inc_ref(v_lctx_775_);
v___x_777_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_777_, 0, v_env_771_);
lean_ctor_set(v___x_777_, 1, v_mctx_774_);
lean_ctor_set(v___x_777_, 2, v_lctx_775_);
lean_ctor_set(v___x_777_, 3, v_options_776_);
v___x_778_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_msgData_764_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(v_msgData_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(lean_object* v_opts_787_, lean_object* v_opt_788_){
_start:
{
lean_object* v_name_789_; lean_object* v_defValue_790_; lean_object* v_map_791_; lean_object* v___x_792_; 
v_name_789_ = lean_ctor_get(v_opt_788_, 0);
v_defValue_790_ = lean_ctor_get(v_opt_788_, 1);
v_map_791_ = lean_ctor_get(v_opts_787_, 0);
v___x_792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_791_, v_name_789_);
if (lean_obj_tag(v___x_792_) == 0)
{
uint8_t v___x_793_; 
v___x_793_ = lean_unbox(v_defValue_790_);
return v___x_793_;
}
else
{
lean_object* v_val_794_; 
v_val_794_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v___x_792_, 1);
if (lean_obj_tag(v_val_794_) == 1)
{
uint8_t v_v_795_; 
v_v_795_ = lean_ctor_get_uint8(v_val_794_, 0);
lean_dec_ref_known(v_val_794_, 0);
return v_v_795_;
}
else
{
uint8_t v___x_796_; 
lean_dec(v_val_794_);
v___x_796_ = lean_unbox(v_defValue_790_);
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_opts_797_, lean_object* v_opt_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(v_opts_797_, v_opt_798_);
lean_dec_ref(v_opt_798_);
lean_dec_ref(v_opts_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_box(1);
v___x_802_ = l_Lean_MessageData_ofFormat(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2));
v___x_807_ = l_Lean_MessageData_ofFormat(v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
return v_x_808_;
}
else
{
lean_object* v_head_810_; lean_object* v_tail_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_833_; 
v_head_810_ = lean_ctor_get(v_x_809_, 0);
v_tail_811_ = lean_ctor_get(v_x_809_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_833_ == 0)
{
v___x_813_ = v_x_809_;
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_tail_811_);
lean_inc(v_head_810_);
lean_dec(v_x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_833_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_before_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_831_; 
v_before_815_ = lean_ctor_get(v_head_810_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_head_810_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_head_810_, 1);
lean_dec(v_unused_832_);
v___x_817_ = v_head_810_;
v_isShared_818_ = v_isSharedCheck_831_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_before_815_);
lean_dec(v_head_810_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_831_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0);
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 7);
lean_ctor_set(v___x_817_, 1, v___x_819_);
lean_ctor_set(v___x_817_, 0, v_x_808_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_x_808_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_830_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 7);
lean_ctor_set(v___x_813_, 1, v___x_822_);
lean_ctor_set(v___x_813_, 0, v___x_821_);
v___x_824_ = v___x_813_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_822_);
v___x_824_ = v_reuseFailAlloc_829_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = l_Lean_MessageData_ofSyntax(v_before_815_);
v___x_826_ = l_Lean_indentD(v___x_825_);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v_x_808_ = v___x_827_;
v_x_809_ = v_tail_811_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_838_ = l_Lean_MessageData_ofFormat(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_839_, lean_object* v_macroStack_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_toCold_843_; lean_object* v_options_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_toCold_843_ = lean_ctor_get(v___y_841_, 0);
v_options_844_ = lean_ctor_get(v_toCold_843_, 2);
v___x_845_ = l_Lean_Elab_pp_macroStack;
v___x_846_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(v_options_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v_macroStack_840_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_msgData_839_);
return v___x_847_;
}
else
{
if (lean_obj_tag(v_macroStack_840_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_msgData_839_);
return v___x_848_;
}
else
{
lean_object* v_head_849_; lean_object* v_after_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_865_; 
v_head_849_ = lean_ctor_get(v_macroStack_840_, 0);
lean_inc(v_head_849_);
v_after_850_ = lean_ctor_get(v_head_849_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_head_849_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_head_849_, 0);
lean_dec(v_unused_866_);
v___x_852_ = v_head_849_;
v_isShared_853_ = v_isSharedCheck_865_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_after_850_);
lean_dec(v_head_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_865_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 7);
lean_ctor_set(v___x_852_, 1, v___x_854_);
lean_ctor_set(v___x_852_, 0, v_msgData_839_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_msgData_839_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_864_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_msgData_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_857_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_MessageData_ofSyntax(v_after_850_);
v___x_860_ = l_Lean_indentD(v___x_859_);
v_msgData_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_861_, 0, v___x_858_);
lean_ctor_set(v_msgData_861_, 1, v___x_860_);
v___x_862_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(v_msgData_861_, v_macroStack_840_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_867_, lean_object* v_macroStack_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_msgData_867_, v_macroStack_868_, v___y_869_);
lean_dec_ref(v___y_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(lean_object* v_msg_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_ref_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v_macroStack_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_ref_880_ = lean_ctor_get(v___y_877_, 2);
v___x_881_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(v_msg_872_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
v_macroStack_883_ = lean_ctor_get(v___y_873_, 1);
v___x_884_ = l_Lean_Elab_getBetterRef(v_ref_880_, v_macroStack_883_);
lean_inc(v_macroStack_883_);
v___x_885_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_a_882_, v_macroStack_883_, v___y_877_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_884_);
lean_ctor_set(v___x_890_, 1, v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg___boxed(lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(lean_object* v_constName_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_env_919_; lean_object* v___x_920_; 
v___x_918_ = lean_st_ref_get(v___y_916_);
v_env_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_ref(v_env_919_);
lean_dec(v___x_918_);
lean_inc(v_constName_910_);
v___x_920_ = l_Lean_isInductiveCore_x3f(v_env_919_, v_constName_910_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_921_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1);
v___x_922_ = 0;
v___x_923_ = l_Lean_MessageData_ofConstName(v_constName_910_, v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_921_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v___x_926_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_927_;
}
else
{
lean_object* v_val_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_constName_910_);
v_val_928_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_920_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_val_928_);
lean_dec(v___x_920_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_val_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___boxed(lean_object* v_constName_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(v_constName_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(lean_object* v_declName_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; 
lean_inc(v_declName_945_);
v___x_953_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(v_declName_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_toConstantVal_955_; lean_object* v_ctors_956_; lean_object* v_type_957_; lean_object* v___f_958_; uint8_t v___x_959_; lean_object* v___x_960_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_toConstantVal_955_ = lean_ctor_get(v_a_954_, 0);
lean_inc_ref(v_toConstantVal_955_);
v_ctors_956_ = lean_ctor_get(v_a_954_, 4);
lean_inc(v_ctors_956_);
lean_dec(v_a_954_);
v_type_957_ = lean_ctor_get(v_toConstantVal_955_, 2);
lean_inc_ref(v_type_957_);
lean_dec_ref(v_toConstantVal_955_);
v___f_958_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed), 11, 2);
lean_closure_set(v___f_958_, 0, v_ctors_956_);
lean_closure_set(v___f_958_, 1, v_declName_945_);
v___x_959_ = 0;
v___x_960_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_957_, v___f_958_, v___x_959_, v___x_959_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
return v___x_960_;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v_declName_945_);
v_a_961_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_953_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_953_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed(lean_object* v_declName_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(v_declName_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_as_978_, v_sz_979_, v_i_980_, v_b_981_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___boxed(lean_object* v_as_990_, lean_object* v_sz_991_, lean_object* v_i_992_, lean_object* v_b_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_991_);
lean_dec(v_sz_991_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(v_as_990_, v_sz_boxed_1001_, v_i_boxed_1002_, v_b_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v_as_990_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(size_t v_sz_1004_, size_t v_i_1005_, lean_object* v_bs_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_1004_, v_i_1005_, v_bs_1006_, v___y_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___boxed(lean_object* v_sz_1015_, lean_object* v_i_1016_, lean_object* v_bs_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
size_t v_sz_boxed_1025_; size_t v_i_boxed_1026_; lean_object* v_res_1027_; 
v_sz_boxed_1025_ = lean_unbox_usize(v_sz_1015_);
lean_dec(v_sz_1015_);
v_i_boxed_1026_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(v_sz_boxed_1025_, v_i_boxed_1026_, v_bs_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(lean_object* v_00_u03b1_1028_, lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v_msg_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(v_00_u03b1_1038_, v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(lean_object* v_msgData_1048_, lean_object* v_macroStack_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_msgData_1048_, v_macroStack_1049_, v___y_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1058_, lean_object* v_macroStack_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(v_msgData_1058_, v_macroStack_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(lean_object* v_declName_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v_env_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1071_ = lean_st_ref_get(v___y_1069_);
v_env_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_ref(v_env_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = l_Lean_isInductiveCore(v_env_1072_, v_declName_1068_);
v___x_1074_ = lean_box(v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v_declName_1076_, v___y_1077_);
lean_dec(v___y_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(lean_object* v_declName_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v_declName_1080_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___boxed(lean_object* v_declName_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(v_declName_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(uint8_t v_____do__lift_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
if (v_____do__lift_1090_ == 0)
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = 1;
v___x_1095_ = lean_box(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = 0;
v___x_1098_ = lean_box(v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_____do__lift_1780__boxed_1104_; lean_object* v_res_1105_; 
v_____do__lift_1780__boxed_1104_ = lean_unbox(v_____do__lift_1100_);
v_res_1105_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(v_____do__lift_1780__boxed_1104_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(lean_object* v_as_1106_, size_t v_i_1107_, size_t v_stop_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_eq(v_i_1107_, v_stop_1108_);
if (v___x_1116_ == 0)
{
uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = 1;
v___x_1118_ = lean_array_uget_borrowed(v_as_1106_, v_i_1107_);
lean_inc(v___x_1118_);
v___x_1119_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v___x_1118_, v___y_1110_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(v___x_1117_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_del_object(v___x_1122_);
goto v___jp_1112_;
}
}
}
else
{
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1139_; 
v_a_1130_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1132_ = v___x_1119_;
v_isShared_1133_ = v_isSharedCheck_1139_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1119_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1139_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_unbox(v_a_1130_);
lean_dec(v_a_1130_);
if (v___x_1134_ == 0)
{
lean_del_object(v___x_1132_);
goto v___jp_1112_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_box(v___x_1117_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1135_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
return v___x_1119_;
}
}
}
else
{
uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = 0;
v___x_1141_ = lean_box(v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
v___jp_1112_:
{
size_t v___x_1113_; size_t v___x_1114_; 
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_add(v_i_1107_, v___x_1113_);
v_i_1107_ = v___x_1114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2___boxed(lean_object* v_as_1143_, lean_object* v_i_1144_, lean_object* v_stop_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
size_t v_i_boxed_1149_; size_t v_stop_boxed_1150_; lean_object* v_res_1151_; 
v_i_boxed_1149_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_stop_boxed_1150_ = lean_unbox_usize(v_stop_1145_);
lean_dec(v_stop_1145_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(v_as_1143_, v_i_boxed_1149_, v_stop_boxed_1150_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_as_1143_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(lean_object* v___x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_Elab_Command_elabCommand(v_a_1157_, v___y_1153_, v___y_1154_);
return v___x_1158_;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1156_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed(lean_object* v___x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(v___x_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(lean_object* v_as_1172_, size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_b_1175_);
return v___x_1180_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; 
v_a_1181_ = lean_array_uget_borrowed(v_as_1172_, v_i_1174_);
lean_inc_n(v_a_1181_, 2);
v___x_1182_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed), 8, 1);
lean_closure_set(v___x_1182_, 0, v_a_1181_);
v___f_1183_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1183_, 0, v___x_1182_);
v___x_1184_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_1181_, v___f_1183_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; 
lean_dec_ref_known(v___x_1184_, 1);
v___x_1185_ = lean_box(0);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1174_, v___x_1186_);
v_i_1174_ = v___x_1187_;
v_b_1175_ = v___x_1185_;
goto _start;
}
else
{
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___boxed(lean_object* v_as_1189_, lean_object* v_sz_1190_, lean_object* v_i_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(v_as_1189_, v_sz_boxed_1196_, v_i_boxed_1197_, v_b_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_as_1189_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(lean_object* v_declNames_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___y_1227_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_array_get_size(v_declNames_1199_);
v___x_1232_ = lean_nat_dec_lt(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(v___x_1232_, v_a_1200_, v_a_1201_);
v___y_1227_ = v___x_1233_;
goto v___jp_1226_;
}
else
{
if (v___x_1232_ == 0)
{
goto v___jp_1203_;
}
else
{
size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = ((size_t)0ULL);
v___x_1235_ = lean_usize_of_nat(v___x_1231_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(v_declNames_1199_, v___x_1234_, v___x_1235_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = lean_unbox(v_a_1237_);
lean_dec(v_a_1237_);
v___x_1239_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(v___x_1238_, v_a_1200_, v_a_1201_);
v___y_1227_ = v___x_1239_;
goto v___jp_1226_;
}
else
{
v___y_1227_ = v___x_1236_;
goto v___jp_1226_;
}
}
}
v___jp_1203_:
{
lean_object* v___x_1204_; size_t v_sz_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1204_ = lean_box(0);
v_sz_1205_ = lean_array_size(v_declNames_1199_);
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(v_declNames_1199_, v_sz_1205_, v___x_1206_, v___x_1204_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1216_; 
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1207_, 0);
lean_dec(v_unused_1217_);
v___x_1209_ = v___x_1207_;
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
else
{
lean_dec(v___x_1207_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = 1;
v___x_1212_ = lean_box(v___x_1211_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_a_1218_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1207_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1207_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
v___jp_1226_:
{
if (lean_obj_tag(v___y_1227_) == 0)
{
lean_object* v_a_1228_; uint8_t v___x_1229_; 
v_a_1228_ = lean_ctor_get(v___y_1227_, 0);
v___x_1229_ = lean_unbox(v_a_1228_);
if (v___x_1229_ == 0)
{
return v___y_1227_;
}
else
{
lean_dec_ref_known(v___y_1227_, 1);
goto v___jp_1203_;
}
}
else
{
return v___y_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___boxed(lean_object* v_declNames_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(v_declNames_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec_ref(v_declNames_1240_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13));
v___x_1248_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_));
v___x_1249_ = l_Lean_Elab_registerDerivingHandler(v___x_1247_, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2____boxed(lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_();
return v_res_1251_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Nonempty(uint8_t builtin) {
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
res = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Nonempty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Nonempty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Nonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Nonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Nonempty(builtin);
}
#ifdef __cplusplus
}
#endif
