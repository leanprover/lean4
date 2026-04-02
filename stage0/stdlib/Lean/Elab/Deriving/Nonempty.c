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
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__62_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__63_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64 = (const lean_object*)&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64_value;
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
lean_dec_ref(v___x_195_);
v___x_197_ = lean_erase_macro_scopes(v_a_196_);
v___x_198_ = l_Lean_Core_mkFreshUserName(v___x_197_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_ref_200_; lean_object* v_quotContext_201_; lean_object* v_currMacroScope_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
v_ref_200_ = lean_ctor_get(v___y_183_, 5);
v_quotContext_201_ = lean_ctor_get(v___y_183_, 10);
v_currMacroScope_202_ = lean_ctor_get(v___y_183_, 11);
v___x_203_ = lean_mk_syntax_ident(v_a_199_);
v___x_204_ = 0;
v___x_205_ = l_Lean_SourceInfo_fromRef(v_ref_200_, v___x_204_);
v___x_206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__0));
lean_inc_n(v___x_205_, 2);
v___x_207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6));
lean_inc(v___x_203_);
v___x_209_ = l_Lean_Syntax_node1(v___x_205_, v___x_208_, v___x_203_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v_a_193_);
v___x_210_ = lean_infer_type(v_a_193_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_210_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
v___x_212_ = lean_whnf(v_a_211_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_261_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___x_212_);
v_fst_214_ = lean_ctor_get(v_b_180_, 0);
v_snd_215_ = lean_ctor_get(v_b_180_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_b_180_);
if (v_isSharedCheck_261_ == 0)
{
v___x_217_ = v_b_180_;
v_isShared_218_ = v_isSharedCheck_261_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v_b_180_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_261_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1);
lean_inc_n(v___x_205_, 3);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_205_);
lean_ctor_set(v___x_220_, 1, v___x_208_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__3));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_205_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_array_push(v_fst_214_, v___x_203_);
v___x_224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__5));
lean_inc_ref(v___x_220_);
lean_inc(v___x_209_);
v___x_225_ = l_Lean_Syntax_node4(v___x_205_, v___x_224_, v___x_207_, v___x_209_, v___x_220_, v___x_222_);
v___x_226_ = lean_array_push(v_snd_215_, v___x_225_);
if (lean_obj_tag(v_a_213_) == 3)
{
lean_object* v_u_227_; lean_object* v___x_228_; 
v_u_227_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_u_227_);
lean_dec_ref(v_a_213_);
v___x_228_ = l_Lean_Meta_decLevel_x3f(v_u_227_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_228_);
if (lean_obj_tag(v_a_229_) == 1)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
lean_dec_ref(v_a_229_);
v___x_230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__7));
v___x_231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__8));
lean_inc_n(v___x_205_, 4);
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_205_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10));
v___x_234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12);
v___x_235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13));
lean_inc(v_currMacroScope_202_);
lean_inc(v_quotContext_201_);
v___x_236_ = l_Lean_addMacroScope(v_quotContext_201_, v___x_235_, v_currMacroScope_202_);
v___x_237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17));
v___x_238_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_205_);
lean_ctor_set(v___x_238_, 1, v___x_234_);
lean_ctor_set(v___x_238_, 2, v___x_236_);
lean_ctor_set(v___x_238_, 3, v___x_237_);
v___x_239_ = l_Lean_Syntax_node2(v___x_205_, v___x_233_, v___x_238_, v___x_209_);
v___x_240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__18));
v___x_241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_205_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = l_Lean_Syntax_node4(v___x_205_, v___x_230_, v___x_232_, v___x_220_, v___x_239_, v___x_241_);
v___x_243_ = lean_array_push(v___x_226_, v___x_242_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_243_);
lean_ctor_set(v___x_217_, 0, v___x_223_);
v___x_245_ = v___x_217_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v_a_187_ = v___x_245_;
goto v___jp_186_;
}
}
else
{
lean_object* v___x_248_; 
lean_dec(v_a_229_);
lean_dec_ref(v___x_220_);
lean_dec(v___x_209_);
lean_dec(v___x_205_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_226_);
lean_ctor_set(v___x_217_, 0, v___x_223_);
v___x_248_ = v___x_217_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_226_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v_a_187_ = v___x_248_;
goto v___jp_186_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v___x_226_);
lean_dec_ref(v___x_223_);
lean_dec_ref(v___x_220_);
lean_del_object(v___x_217_);
lean_dec(v___x_209_);
lean_dec(v___x_205_);
v_a_250_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_228_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_228_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
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
else
{
lean_object* v___x_259_; 
lean_dec_ref(v___x_220_);
lean_dec(v_a_213_);
lean_dec(v___x_209_);
lean_dec(v___x_205_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_226_);
lean_ctor_set(v___x_217_, 0, v___x_223_);
v___x_259_ = v___x_217_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_226_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
v_a_187_ = v___x_259_;
goto v___jp_186_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v___x_209_);
lean_dec_ref(v___x_207_);
lean_dec(v___x_205_);
lean_dec(v___x_203_);
lean_dec_ref(v_b_180_);
v_a_262_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_212_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_212_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v___x_209_);
lean_dec_ref(v___x_207_);
lean_dec(v___x_205_);
lean_dec(v___x_203_);
lean_dec_ref(v_b_180_);
v_a_270_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_210_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_210_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_b_180_);
v_a_278_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_198_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_198_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_b_180_);
v_a_286_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_195_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_195_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___boxed(lean_object* v_as_294_, lean_object* v_sz_295_, lean_object* v_i_296_, lean_object* v_b_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
size_t v_sz_boxed_303_; size_t v_i_boxed_304_; lean_object* v_res_305_; 
v_sz_boxed_303_ = lean_unbox_usize(v_sz_295_);
lean_dec(v_sz_295_);
v_i_boxed_304_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_res_305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_as_294_, v_sz_boxed_303_, v_i_boxed_304_, v_b_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec_ref(v_as_294_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(size_t v_sz_306_, size_t v_i_307_, lean_object* v_bs_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = lean_usize_dec_lt(v_i_307_, v_sz_306_);
if (v___x_309_ == 0)
{
return v_bs_308_;
}
else
{
lean_object* v_v_310_; lean_object* v___x_311_; lean_object* v_bs_x27_312_; size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; 
v_v_310_ = lean_array_uget(v_bs_308_, v_i_307_);
v___x_311_ = lean_unsigned_to_nat(0u);
v_bs_x27_312_ = lean_array_uset(v_bs_308_, v_i_307_, v___x_311_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_add(v_i_307_, v___x_313_);
v___x_315_ = lean_array_uset(v_bs_x27_312_, v_i_307_, v_v_310_);
v_i_307_ = v___x_314_;
v_bs_308_ = v___x_315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4___boxed(lean_object* v_sz_317_, lean_object* v_i_318_, lean_object* v_bs_319_){
_start:
{
size_t v_sz_boxed_320_; size_t v_i_boxed_321_; lean_object* v_res_322_; 
v_sz_boxed_320_ = lean_unbox_usize(v_sz_317_);
lean_dec(v_sz_317_);
v_i_boxed_321_ = lean_unbox_usize(v_i_318_);
lean_dec(v_i_318_);
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(v_sz_boxed_320_, v_i_boxed_321_, v_bs_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(size_t v_sz_323_, size_t v_i_324_, lean_object* v_bs_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_326_ == 0)
{
return v_bs_325_;
}
else
{
lean_object* v_v_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_v_327_ = lean_array_uget(v_bs_325_, v_i_324_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_325_, v_i_324_, v___x_328_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_324_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_329_, v_i_324_, v_v_327_);
v_i_324_ = v___x_331_;
v_bs_325_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3___boxed(lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_bs_336_){
_start:
{
size_t v_sz_boxed_337_; size_t v_i_boxed_338_; lean_object* v_res_339_; 
v_sz_boxed_337_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(v_sz_boxed_337_, v_i_boxed_338_, v_bs_336_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__10));
v___x_368_ = l_String_toRawSubstring_x27(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(size_t v_sz_380_, size_t v_i_381_, lean_object* v_bs_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_lt(v_i_381_, v_sz_380_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_bs_382_);
return v___x_386_;
}
else
{
lean_object* v_ref_387_; lean_object* v_quotContext_388_; lean_object* v_currMacroScope_389_; lean_object* v_v_390_; lean_object* v___x_391_; lean_object* v_bs_x27_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v_ref_387_ = lean_ctor_get(v___y_383_, 5);
v_quotContext_388_ = lean_ctor_get(v___y_383_, 10);
v_currMacroScope_389_ = lean_ctor_get(v___y_383_, 11);
v_v_390_ = lean_array_uget(v_bs_382_, v_i_381_);
v___x_391_ = lean_unsigned_to_nat(0u);
v_bs_x27_392_ = lean_array_uset(v_bs_382_, v_i_381_, v___x_391_);
v___x_393_ = 0;
v___x_394_ = l_Lean_SourceInfo_fromRef(v_ref_387_, v___x_393_);
v___x_395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__1));
v___x_396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__2));
v___x_397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__3));
lean_inc_n(v___x_394_, 8);
v___x_398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_394_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5));
v___x_400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6));
v___x_401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_394_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_mkCIdent(v_v_390_);
v___x_403_ = l_Lean_Syntax_node2(v___x_394_, v___x_399_, v___x_401_, v___x_402_);
v___x_404_ = l_Lean_Syntax_node2(v___x_394_, v___x_397_, v___x_398_, v___x_403_);
v___x_405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__7));
v___x_406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_394_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__8));
v___x_408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__9));
v___x_409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_394_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
v___x_410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__11);
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__14));
lean_inc(v_currMacroScope_389_);
lean_inc(v_quotContext_388_);
v___x_412_ = l_Lean_addMacroScope(v_quotContext_388_, v___x_411_, v_currMacroScope_389_);
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__16));
v___x_414_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_414_, 0, v___x_394_);
lean_ctor_set(v___x_414_, 1, v___x_410_);
lean_ctor_set(v___x_414_, 2, v___x_412_);
lean_ctor_set(v___x_414_, 3, v___x_413_);
v___x_415_ = l_Lean_Syntax_node2(v___x_394_, v___x_408_, v___x_409_, v___x_414_);
v___x_416_ = l_Lean_Syntax_node3(v___x_394_, v___x_395_, v___x_404_, v___x_406_, v___x_415_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_381_, v___x_417_);
v___x_419_ = lean_array_uset(v_bs_x27_392_, v_i_381_, v___x_416_);
v_i_381_ = v___x_418_;
v_bs_382_ = v___x_419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___boxed(lean_object* v_sz_421_, lean_object* v_i_422_, lean_object* v_bs_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_421_);
lean_dec(v_sz_421_);
v_i_boxed_427_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_boxed_426_, v_i_boxed_427_, v_bs_423_, v___y_424_);
lean_dec_ref(v___y_424_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__27));
v___x_501_ = l_String_toRawSubstring_x27(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(lean_object* v_ctors_592_, lean_object* v_declName_593_, lean_object* v_paramsIndices_594_, lean_object* v_x_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; size_t v_sz_604_; size_t v___x_605_; lean_object* v___x_606_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__1));
v_sz_604_ = lean_array_size(v_paramsIndices_594_);
v___x_605_ = ((size_t)0ULL);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_paramsIndices_594_, v_sz_604_, v___x_605_, v___x_603_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; size_t v_sz_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = lean_array_mk(v_ctors_592_);
v_sz_609_ = lean_array_size(v___x_608_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_609_, v___x_605_, v___x_608_, v___y_600_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_724_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_724_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_724_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_724_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_723_; 
v_fst_615_ = lean_ctor_get(v_a_607_, 0);
v_snd_616_ = lean_ctor_get(v_a_607_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_723_ == 0)
{
v___x_618_ = v_a_607_;
v_isShared_619_ = v_isSharedCheck_723_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_a_607_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_723_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_ref_620_; lean_object* v_quotContext_621_; lean_object* v_currMacroScope_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v_ref_620_ = lean_ctor_get(v___y_600_, 5);
v_quotContext_621_ = lean_ctor_get(v___y_600_, 10);
v_currMacroScope_622_ = lean_ctor_get(v___y_600_, 11);
v___x_623_ = 0;
v___x_624_ = l_Lean_SourceInfo_fromRef(v_ref_620_, v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__3));
v___x_626_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__4));
v___x_627_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__5));
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__6));
lean_inc(v___x_624_);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 2);
lean_ctor_set(v___x_618_, 1, v___x_627_);
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_630_ = v___x_618_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_627_);
v___x_630_ = v_reuseFailAlloc_722_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; size_t v_sz_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; size_t v_sz_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; size_t v_sz_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__6));
v___x_632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__1);
v_sz_633_ = lean_array_size(v_snd_616_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__3(v_sz_633_, v___x_605_, v_snd_616_);
v___x_635_ = l_Array_append___redArg(v___x_632_, v___x_634_);
lean_dec_ref(v___x_634_);
lean_inc_n(v___x_624_, 40);
v___x_636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_636_, 0, v___x_624_);
lean_ctor_set(v___x_636_, 1, v___x_631_);
lean_ctor_set(v___x_636_, 2, v___x_635_);
v___x_637_ = l_Lean_Syntax_node2(v___x_624_, v___x_628_, v___x_630_, v___x_636_);
v___x_638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_624_);
lean_ctor_set(v___x_638_, 1, v___x_625_);
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__8));
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__10));
v___x_641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_624_);
lean_ctor_set(v___x_641_, 1, v___x_631_);
lean_ctor_set(v___x_641_, 2, v___x_632_);
lean_inc_ref_n(v___x_641_, 13);
v___x_642_ = l_Lean_Syntax_node7(v___x_624_, v___x_640_, v___x_641_, v___x_641_, v___x_641_, v___x_641_, v___x_641_, v___x_641_, v___x_641_);
v___x_643_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__11));
v___x_644_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__12));
v___x_645_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__14));
v___x_646_ = l_Lean_Syntax_node1(v___x_624_, v___x_645_, v___x_641_);
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_624_);
lean_ctor_set(v___x_647_, 1, v___x_643_);
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__16));
v___x_649_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__18));
v___x_650_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__19));
v___x_651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_624_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__10));
v___x_653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__12);
v___x_654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13));
lean_inc_n(v_currMacroScope_622_, 2);
lean_inc_n(v_quotContext_621_, 2);
v___x_655_ = l_Lean_addMacroScope(v_quotContext_621_, v___x_654_, v_currMacroScope_622_);
v___x_656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__17));
v___x_657_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_657_, 0, v___x_624_);
lean_ctor_set(v___x_657_, 1, v___x_653_);
lean_ctor_set(v___x_657_, 2, v___x_655_);
lean_ctor_set(v___x_657_, 3, v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__21));
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__23));
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__24));
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_624_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__26));
v___x_663_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28, &l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28_once, _init_l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__28);
v___x_664_ = lean_box(0);
v___x_665_ = l_Lean_addMacroScope(v_quotContext_621_, v___x_664_, v_currMacroScope_622_);
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__49));
v___x_667_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_667_, 0, v___x_624_);
lean_ctor_set(v___x_667_, 1, v___x_663_);
lean_ctor_set(v___x_667_, 2, v___x_665_);
lean_ctor_set(v___x_667_, 3, v___x_666_);
v___x_668_ = l_Lean_Syntax_node1(v___x_624_, v___x_662_, v___x_667_);
v___x_669_ = l_Lean_Syntax_node2(v___x_624_, v___x_659_, v___x_661_, v___x_668_);
v___x_670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__5));
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg___closed__6));
v___x_672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_624_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_mkCIdent(v_declName_593_);
v___x_674_ = l_Lean_Syntax_node2(v___x_624_, v___x_670_, v___x_672_, v___x_673_);
v_sz_675_ = lean_array_size(v_fst_615_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__4(v_sz_675_, v___x_605_, v_fst_615_);
v___x_677_ = l_Array_append___redArg(v___x_632_, v___x_676_);
lean_dec_ref(v___x_676_);
v___x_678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_678_, 0, v___x_624_);
lean_ctor_set(v___x_678_, 1, v___x_631_);
lean_ctor_set(v___x_678_, 2, v___x_677_);
v___x_679_ = l_Lean_Syntax_node2(v___x_624_, v___x_652_, v___x_674_, v___x_678_);
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__50));
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_624_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_Syntax_node3(v___x_624_, v___x_658_, v___x_669_, v___x_679_, v___x_681_);
v___x_683_ = l_Lean_Syntax_node1(v___x_624_, v___x_631_, v___x_682_);
v___x_684_ = l_Lean_Syntax_node2(v___x_624_, v___x_652_, v___x_657_, v___x_683_);
v___x_685_ = l_Lean_Syntax_node2(v___x_624_, v___x_649_, v___x_651_, v___x_684_);
v___x_686_ = l_Lean_Syntax_node2(v___x_624_, v___x_648_, v___x_641_, v___x_685_);
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__52));
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__53));
v___x_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_624_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__55));
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__56));
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_624_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__8));
v___x_694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5___closed__4));
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__57));
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__58));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_624_);
lean_ctor_set(v___x_697_, 1, v___x_695_);
v___x_698_ = l_Lean_Syntax_node1(v___x_624_, v___x_696_, v___x_697_);
v___x_699_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__59));
v___x_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_624_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__60));
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__61));
v___x_703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_624_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
v_sz_704_ = lean_array_size(v_a_611_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__5(v___x_624_, v_sz_704_, v___x_605_, v_a_611_);
v___x_706_ = l_Array_append___redArg(v___x_632_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v___x_624_);
lean_ctor_set(v___x_707_, 1, v___x_631_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
v___x_708_ = l_Lean_Syntax_node2(v___x_624_, v___x_702_, v___x_703_, v___x_707_);
v___x_709_ = l_Lean_Syntax_node3(v___x_624_, v___x_631_, v___x_698_, v___x_700_, v___x_708_);
v___x_710_ = l_Lean_Syntax_node1(v___x_624_, v___x_694_, v___x_709_);
v___x_711_ = l_Lean_Syntax_node1(v___x_624_, v___x_693_, v___x_710_);
v___x_712_ = l_Lean_Syntax_node2(v___x_624_, v___x_690_, v___x_692_, v___x_711_);
v___x_713_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___closed__64));
v___x_714_ = l_Lean_Syntax_node2(v___x_624_, v___x_713_, v___x_641_, v___x_641_);
v___x_715_ = l_Lean_Syntax_node4(v___x_624_, v___x_687_, v___x_689_, v___x_712_, v___x_714_, v___x_641_);
v___x_716_ = l_Lean_Syntax_node6(v___x_624_, v___x_644_, v___x_646_, v___x_647_, v___x_641_, v___x_641_, v___x_686_, v___x_715_);
v___x_717_ = l_Lean_Syntax_node2(v___x_624_, v___x_639_, v___x_642_, v___x_716_);
v___x_718_ = l_Lean_Syntax_node3(v___x_624_, v___x_626_, v___x_637_, v___x_638_, v___x_717_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_718_);
v___x_720_ = v___x_613_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_a_607_);
lean_dec(v_declName_593_);
v_a_725_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_610_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_610_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_declName_593_);
lean_dec(v_ctors_592_);
v_a_733_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_606_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_606_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed(lean_object* v_ctors_741_, lean_object* v_declName_742_, lean_object* v_paramsIndices_743_, lean_object* v_x_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0(v_ctors_741_, v_declName_742_, v_paramsIndices_743_, v_x_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v_x_744_);
lean_dec_ref(v_paramsIndices_743_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(lean_object* v_msgData_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_env_760_; lean_object* v___x_761_; lean_object* v_mctx_762_; lean_object* v_lctx_763_; lean_object* v_options_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_759_ = lean_st_ref_get(v___y_757_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_env_760_);
lean_dec(v___x_759_);
v___x_761_ = lean_st_ref_get(v___y_755_);
v_mctx_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc_ref(v_mctx_762_);
lean_dec(v___x_761_);
v_lctx_763_ = lean_ctor_get(v___y_754_, 2);
v_options_764_ = lean_ctor_get(v___y_756_, 2);
lean_inc_ref(v_options_764_);
lean_inc_ref(v_lctx_763_);
v___x_765_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_765_, 0, v_env_760_);
lean_ctor_set(v___x_765_, 1, v_mctx_762_);
lean_ctor_set(v___x_765_, 2, v_lctx_763_);
lean_ctor_set(v___x_765_, 3, v_options_764_);
v___x_766_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_msgData_753_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(v_msgData_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(lean_object* v_opts_775_, lean_object* v_opt_776_){
_start:
{
lean_object* v_name_777_; lean_object* v_defValue_778_; lean_object* v_map_779_; lean_object* v___x_780_; 
v_name_777_ = lean_ctor_get(v_opt_776_, 0);
v_defValue_778_ = lean_ctor_get(v_opt_776_, 1);
v_map_779_ = lean_ctor_get(v_opts_775_, 0);
v___x_780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_779_, v_name_777_);
if (lean_obj_tag(v___x_780_) == 0)
{
uint8_t v___x_781_; 
v___x_781_ = lean_unbox(v_defValue_778_);
return v___x_781_;
}
else
{
lean_object* v_val_782_; 
v_val_782_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v___x_780_);
if (lean_obj_tag(v_val_782_) == 1)
{
uint8_t v_v_783_; 
v_v_783_ = lean_ctor_get_uint8(v_val_782_, 0);
lean_dec_ref(v_val_782_);
return v_v_783_;
}
else
{
uint8_t v___x_784_; 
lean_dec(v_val_782_);
v___x_784_ = lean_unbox(v_defValue_778_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9___boxed(lean_object* v_opts_785_, lean_object* v_opt_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(v_opts_785_, v_opt_786_);
lean_dec_ref(v_opt_786_);
lean_dec_ref(v_opts_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(1);
v___x_790_ = l_Lean_MessageData_ofFormat(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__2));
v___x_795_ = l_Lean_MessageData_ofFormat(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
return v_x_796_;
}
else
{
lean_object* v_head_798_; lean_object* v_tail_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_821_; 
v_head_798_ = lean_ctor_get(v_x_797_, 0);
v_tail_799_ = lean_ctor_get(v_x_797_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_821_ == 0)
{
v___x_801_ = v_x_797_;
v_isShared_802_ = v_isSharedCheck_821_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_tail_799_);
lean_inc(v_head_798_);
lean_dec(v_x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_821_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_before_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_819_; 
v_before_803_ = lean_ctor_get(v_head_798_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_head_798_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_head_798_, 1);
lean_dec(v_unused_820_);
v___x_805_ = v_head_798_;
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_before_803_);
lean_dec(v_head_798_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_819_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 7);
lean_ctor_set(v___x_805_, 1, v___x_807_);
lean_ctor_set(v___x_805_, 0, v_x_796_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_x_796_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_818_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__3);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 7);
lean_ctor_set(v___x_801_, 1, v___x_810_);
lean_ctor_set(v___x_801_, 0, v___x_809_);
v___x_812_ = v___x_801_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_817_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_MessageData_ofSyntax(v_before_803_);
v___x_814_ = l_Lean_indentD(v___x_813_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_812_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v_x_796_ = v___x_815_;
v_x_797_ = v_tail_799_;
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
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_826_ = l_Lean_MessageData_ofFormat(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_827_, lean_object* v_macroStack_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_options_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_options_831_ = lean_ctor_get(v___y_829_, 2);
v___x_832_ = l_Lean_Elab_pp_macroStack;
v___x_833_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__9(v_options_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_macroStack_828_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_msgData_827_);
return v___x_834_;
}
else
{
if (lean_obj_tag(v_macroStack_828_) == 0)
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_msgData_827_);
return v___x_835_;
}
else
{
lean_object* v_head_836_; lean_object* v_after_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_852_; 
v_head_836_ = lean_ctor_get(v_macroStack_828_, 0);
lean_inc(v_head_836_);
v_after_837_ = lean_ctor_get(v_head_836_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_head_836_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_head_836_, 0);
lean_dec(v_unused_853_);
v___x_839_ = v_head_836_;
v_isShared_840_ = v_isSharedCheck_852_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_after_837_);
lean_dec(v_head_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_852_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10___closed__0);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 7);
lean_ctor_set(v___x_839_, 1, v___x_841_);
lean_ctor_set(v___x_839_, 0, v_msgData_827_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_msgData_827_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_851_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_msgData_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_844_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_MessageData_ofSyntax(v_after_837_);
v___x_847_ = l_Lean_indentD(v___x_846_);
v_msgData_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_848_, 0, v___x_845_);
lean_ctor_set(v_msgData_848_, 1, v___x_847_);
v___x_849_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3_spec__10(v_msgData_848_, v_macroStack_828_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_854_, lean_object* v_macroStack_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_msgData_854_, v_macroStack_855_, v___y_856_);
lean_dec_ref(v___y_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_ref_867_; lean_object* v___x_868_; lean_object* v_a_869_; lean_object* v_macroStack_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_ref_867_ = lean_ctor_get(v___y_864_, 5);
v___x_868_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__2(v_msg_859_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref(v___x_868_);
v_macroStack_870_ = lean_ctor_get(v___y_860_, 1);
lean_inc_n(v_macroStack_870_, 2);
v___x_871_ = l_Lean_Elab_getBetterRef(v_ref_867_, v_macroStack_870_);
v___x_872_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_a_869_, v_macroStack_870_, v___y_864_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_871_);
lean_ctor_set(v___x_877_, 1, v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg___boxed(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v_msg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_890_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__0));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__2));
v___x_896_ = l_Lean_stringToMessageData(v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(lean_object* v_constName_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_env_906_; lean_object* v___x_907_; 
v___x_905_ = lean_st_ref_get(v___y_903_);
v_env_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_906_);
lean_dec(v___x_905_);
lean_inc(v_constName_897_);
v___x_907_ = l_Lean_isInductiveCore_x3f(v_env_906_, v_constName_897_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_908_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__1);
v___x_909_ = 0;
v___x_910_ = l_Lean_MessageData_ofConstName(v_constName_897_, v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_908_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___closed__3);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v___x_913_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_914_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_constName_897_);
v_val_915_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_907_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_val_915_);
lean_dec(v___x_907_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_val_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0___boxed(lean_object* v_constName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(v_constName_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(lean_object* v_declName_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; 
lean_inc(v_declName_932_);
v___x_940_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0(v_declName_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_toConstantVal_942_; lean_object* v_ctors_943_; lean_object* v_type_944_; lean_object* v___f_945_; uint8_t v___x_946_; lean_object* v___x_947_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref(v___x_940_);
v_toConstantVal_942_ = lean_ctor_get(v_a_941_, 0);
lean_inc_ref(v_toConstantVal_942_);
v_ctors_943_ = lean_ctor_get(v_a_941_, 4);
lean_inc(v_ctors_943_);
lean_dec(v_a_941_);
v_type_944_ = lean_ctor_get(v_toConstantVal_942_, 2);
lean_inc_ref(v_type_944_);
lean_dec_ref(v_toConstantVal_942_);
v___f_945_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___lam__0___boxed), 11, 2);
lean_closure_set(v___f_945_, 0, v_ctors_943_);
lean_closure_set(v___f_945_, 1, v_declName_932_);
v___x_946_ = 0;
v___x_947_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__6___redArg(v_type_944_, v___f_945_, v___x_946_, v___x_946_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_947_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_declName_932_);
v_a_948_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_940_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_940_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed(lean_object* v_declName_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance(v_declName_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(lean_object* v_as_965_, size_t v_sz_966_, size_t v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg(v_as_965_, v_sz_966_, v_i_967_, v_b_968_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___boxed(lean_object* v_as_977_, lean_object* v_sz_978_, lean_object* v_i_979_, lean_object* v_b_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
size_t v_sz_boxed_988_; size_t v_i_boxed_989_; lean_object* v_res_990_; 
v_sz_boxed_988_ = lean_unbox_usize(v_sz_978_);
lean_dec(v_sz_978_);
v_i_boxed_989_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_res_990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1(v_as_977_, v_sz_boxed_988_, v_i_boxed_989_, v_b_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec_ref(v_as_977_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(size_t v_sz_991_, size_t v_i_992_, lean_object* v_bs_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___redArg(v_sz_991_, v_i_992_, v_bs_993_, v___y_998_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2___boxed(lean_object* v_sz_1002_, lean_object* v_i_1003_, lean_object* v_bs_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
size_t v_sz_boxed_1012_; size_t v_i_boxed_1013_; lean_object* v_res_1014_; 
v_sz_boxed_1012_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1013_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__2(v_sz_boxed_1012_, v_i_boxed_1013_, v_bs_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(lean_object* v_00_u03b1_1015_, lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___redArg(v_msg_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0(v_00_u03b1_1025_, v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(lean_object* v_msgData_1035_, lean_object* v_macroStack_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___redArg(v_msgData_1035_, v_macroStack_1036_, v___y_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1045_, lean_object* v_macroStack_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__0_spec__0_spec__3(v_msgData_1045_, v_macroStack_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(lean_object* v_declName_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v_env_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = lean_st_ref_get(v___y_1056_);
v_env_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_ref(v_env_1059_);
lean_dec(v___x_1058_);
v___x_1060_ = l_Lean_isInductiveCore(v_env_1059_, v_declName_1055_);
v___x_1061_ = lean_box(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v_declName_1063_, v___y_1064_);
lean_dec(v___y_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(lean_object* v_declName_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v_declName_1067_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___boxed(lean_object* v_declName_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1(v_declName_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(uint8_t v_____do__lift_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
if (v_____do__lift_1077_ == 0)
{
uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = 1;
v___x_1082_ = lean_box(v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
else
{
uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = 0;
v___x_1085_ = lean_box(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v_____do__lift_1888__boxed_1091_; lean_object* v_res_1092_; 
v_____do__lift_1888__boxed_1091_ = lean_unbox(v_____do__lift_1087_);
v_res_1092_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(v_____do__lift_1888__boxed_1091_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(lean_object* v_as_1093_, size_t v_i_1094_, size_t v_stop_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_usize_dec_eq(v_i_1094_, v_stop_1095_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; uint8_t v_a_1102_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1100_ = 1;
v___x_1108_ = lean_array_uget_borrowed(v_as_1093_, v_i_1094_);
lean_inc(v___x_1108_);
v___x_1109_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__1___redArg(v___x_1108_, v___y_1097_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1119_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_unbox(v_a_1110_);
lean_dec(v_a_1110_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(v___x_1100_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1115_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
else
{
lean_del_object(v___x_1112_);
v_a_1102_ = v___x_1099_;
goto v___jp_1101_;
}
}
}
else
{
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1120_; uint8_t v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1109_);
v___x_1121_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
v_a_1102_ = v___x_1121_;
goto v___jp_1101_;
}
else
{
return v___x_1109_;
}
}
v___jp_1101_:
{
if (v_a_1102_ == 0)
{
size_t v___x_1103_; size_t v___x_1104_; 
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_add(v_i_1094_, v___x_1103_);
v_i_1094_ = v___x_1104_;
goto _start;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_box(v___x_1100_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
}
else
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = 0;
v___x_1123_ = lean_box(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2___boxed(lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_stop_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; lean_object* v_res_1133_; 
v_i_boxed_1131_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1127_);
lean_dec(v_stop_1127_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(v_as_1125_, v_i_boxed_1131_, v_stop_boxed_1132_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_as_1125_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(lean_object* v___x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = l_Lean_Elab_Command_elabCommand(v_a_1139_, v___y_1135_, v___y_1136_);
return v___x_1140_;
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1138_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1138_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed(lean_object* v___x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0(v___x_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(lean_object* v_as_1154_, size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1157_);
return v___x_1162_;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_array_uget_borrowed(v_as_1154_, v_i_1156_);
lean_inc_n(v_a_1163_, 2);
v___x_1164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance___boxed), 8, 1);
lean_closure_set(v___x_1164_, 0, v_a_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1165_, 0, v___x_1164_);
v___x_1166_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_1163_, v___f_1165_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; 
lean_dec_ref(v___x_1166_);
v___x_1167_ = lean_box(0);
v___x_1168_ = ((size_t)1ULL);
v___x_1169_ = lean_usize_add(v_i_1156_, v___x_1168_);
v_i_1156_ = v___x_1169_;
v_b_1157_ = v___x_1167_;
goto _start;
}
else
{
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0___boxed(lean_object* v_as_1171_, lean_object* v_sz_1172_, lean_object* v_i_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
size_t v_sz_boxed_1178_; size_t v_i_boxed_1179_; lean_object* v_res_1180_; 
v_sz_boxed_1178_ = lean_unbox_usize(v_sz_1172_);
lean_dec(v_sz_1172_);
v_i_boxed_1179_ = lean_unbox_usize(v_i_1173_);
lean_dec(v_i_1173_);
v_res_1180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(v_as_1171_, v_sz_boxed_1178_, v_i_boxed_1179_, v_b_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_as_1171_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(lean_object* v_declNames_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___y_1209_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_get_size(v_declNames_1181_);
v___x_1214_ = lean_nat_dec_lt(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(v___x_1214_, v_a_1182_, v_a_1183_);
v___y_1209_ = v___x_1215_;
goto v___jp_1208_;
}
else
{
if (v___x_1214_ == 0)
{
goto v___jp_1185_;
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1213_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__2(v_declNames_1181_, v___x_1216_, v___x_1217_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = lean_unbox(v_a_1219_);
lean_dec(v_a_1219_);
v___x_1221_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___lam__0(v___x_1220_, v_a_1182_, v_a_1183_);
v___y_1209_ = v___x_1221_;
goto v___jp_1208_;
}
else
{
v___y_1209_ = v___x_1218_;
goto v___jp_1208_;
}
}
}
v___jp_1185_:
{
lean_object* v___x_1186_; size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1186_ = lean_box(0);
v_sz_1187_ = lean_array_size(v_declNames_1181_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkNonemptyInstanceHandler_spec__0(v_declNames_1181_, v_sz_1187_, v___x_1188_, v___x_1186_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1189_, 0);
lean_dec(v_unused_1199_);
v___x_1191_ = v___x_1189_;
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v___x_1189_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = 1;
v___x_1194_ = lean_box(v___x_1193_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1189_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1189_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
v___jp_1208_:
{
if (lean_obj_tag(v___y_1209_) == 0)
{
lean_object* v_a_1210_; uint8_t v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___y_1209_, 0);
v___x_1211_ = lean_unbox(v_a_1210_);
if (v___x_1211_ == 0)
{
return v___y_1209_;
}
else
{
lean_dec_ref(v___y_1209_);
goto v___jp_1185_;
}
}
else
{
return v___y_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkNonemptyInstanceHandler___boxed(lean_object* v_declNames_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Elab_Deriving_mkNonemptyInstanceHandler(v_declNames_1222_, v_a_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec_ref(v_declNames_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_mkNonemptyInstance_spec__1___redArg___closed__13));
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_));
v___x_1231_ = l_Lean_Elab_registerDerivingHandler(v___x_1229_, v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2____boxed(lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Elab_Deriving_Nonempty_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Nonempty_1889502729____hygCtx___hyg_2_();
return v_res_1233_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Nonempty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
