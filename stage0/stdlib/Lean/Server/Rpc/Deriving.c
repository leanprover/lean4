// Lean compiler output
// Module: Lean.Server.Rpc.Deriving
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_Term_matchAlt(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Server_RpcEncodable_isOptField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Server_RpcEncodable_isOptField___closed__0 = (const lean_object*)&l_Lean_Server_RpcEncodable_isOptField___closed__0_value;
static lean_once_cell_t l_Lean_Server_RpcEncodable_isOptField___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_RpcEncodable_isOptField___closed__1;
LEAN_EXPORT uint8_t l_Lean_Server_RpcEncodable_isOptField(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_isOptField___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "structExplicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 255, 55, 101, 203, 12, 116, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RpcEncodable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Json"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcEncode"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(181, 130, 28, 14, 164, 108, 68, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(147, 95, 3, 206, 143, 66, 59, 169)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcDecode"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(18, 61, 22, 59, 236, 209, 187, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(220, 0, 93, 28, 42, 216, 37, 123)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mapM"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(58, 78, 170, 251, 181, 31, 172, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__rpcref"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(120, 248, 178, 198, 26, 146, 90, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "'__rpcref' is reserved and cannot be used as a field name. See the `RpcEncodable` docstring."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8_value),LEAN_SCALAR_PTR_LITERAL(180, 236, 187, 15, 83, 171, 117, 65)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "structureTk"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10_value),LEAN_SCALAR_PTR_LITERAL(132, 164, 13, 167, 248, 219, 132, 242)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "RpcEncodablePacket"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14_value),LEAN_SCALAR_PTR_LITERAL(59, 154, 188, 20, 17, 205, 207, 181)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structFields"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18_value),LEAN_SCALAR_PTR_LITERAL(162, 20, 124, 55, 90, 140, 156, 83)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optDeriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20_value),LEAN_SCALAR_PTR_LITERAL(215, 163, 253, 206, 79, 89, 101, 240)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "derivingClass"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value),LEAN_SCALAR_PTR_LITERAL(71, 164, 144, 68, 145, 86, 212, 243)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FromJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value),LEAN_SCALAR_PTR_LITERAL(9, 26, 128, 190, 189, 230, 248, 17)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value),LEAN_SCALAR_PTR_LITERAL(90, 244, 120, 131, 70, 154, 113, 6)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42_value),LEAN_SCALAR_PTR_LITERAL(65, 79, 35, 19, 21, 38, 89, 10)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "variable"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44_value),LEAN_SCALAR_PTR_LITERAL(250, 93, 226, 106, 76, 14, 69, 165)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 110, 25, 5, 88, 138, 0, 41)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "enc"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value),LEAN_SCALAR_PTR_LITERAL(127, 112, 184, 188, 166, 208, 172, 147)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 154, 178, 201, 214, 183, 192)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value),LEAN_SCALAR_PTR_LITERAL(112, 200, 227, 76, 90, 242, 6, 135)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value),LEAN_SCALAR_PTR_LITERAL(240, 112, 235, 135, 88, 35, 83, 81)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "j"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_value),LEAN_SCALAR_PTR_LITERAL(71, 110, 153, 29, 75, 133, 244, 52)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fromJson\?"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value),LEAN_SCALAR_PTR_LITERAL(3, 54, 193, 250, 66, 68, 188, 53)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value),LEAN_SCALAR_PTR_LITERAL(196, 88, 105, 59, 236, 221, 213, 61)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 131, 12, 184, 158, 202, 243, 28)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "for structure "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with params "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "'__rpcref' is reserved and cannot be used as an argument name. See the `RpcEncodable` docstring."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 61, 118, 113, 180, 158, 239, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "constructor name not a string: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 178, 72, 69, 244, 64, 6, 60)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(55, 91, 239, 116, 115, 0, 62, 115)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pkt"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19_value),LEAN_SCALAR_PTR_LITERAL(182, 192, 230, 127, 128, 175, 248, 240)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<|_"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 38, 96, 140, 215, 46, 31, 82)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<|"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "for inductive "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "indexed inductive families are not supported"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "mutually inductive types are not supported"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(79, 45, 83, 138, 97, 177, 55, 171)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rpc"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 191, 146, 242, 66, 17, 254, 170)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value),LEAN_SCALAR_PTR_LITERAL(158, 127, 243, 163, 48, 99, 68, 29)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(103, 87, 172, 78, 42, 229, 166, 12)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 39, 125, 197, 167, 200, 226, 135)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(79, 198, 180, 110, 20, 95, 155, 100)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 214, 222, 162, 111, 144, 143, 232)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 1, 218, 74, 254, 184, 128, 80)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 167, 112, 150, 119, 225, 52, 250)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 60, 176, 162, 23, 211, 36, 203)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(201, 123, 171, 151, 210, 10, 201, 136)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 91, 41, 51, 232, 164, 71, 24)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__19_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value),LEAN_SCALAR_PTR_LITERAL(232, 134, 14, 149, 197, 132, 95, 130)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__19_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__19_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__20_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__19_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)(((size_t)(198155338) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(176, 10, 214, 168, 206, 250, 43, 6)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__20_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__20_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__21_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__21_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__21_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__22_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__20_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__21_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 61, 5, 155, 136, 186, 134, 171)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__22_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__22_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__23_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__23_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__23_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__24_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__22_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__23_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 244, 206, 133, 19, 32, 154, 234)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__24_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__24_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__25_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__24_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(170, 1, 9, 6, 68, 226, 179, 52)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__25_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__25_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Server_RpcEncodable_isOptField___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_Server_RpcEncodable_isOptField___closed__0));
v___x_3_ = lean_string_utf8_byte_size(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RpcEncodable_isOptField(lean_object* v_n_4_){
_start:
{
uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_5_ = 1;
v___x_6_ = l_Lean_Name_toString(v_n_4_, v___x_5_);
v___x_7_ = ((lean_object*)(l_Lean_Server_RpcEncodable_isOptField___closed__0));
v___x_8_ = lean_string_utf8_byte_size(v___x_6_);
v___x_9_ = lean_obj_once(&l_Lean_Server_RpcEncodable_isOptField___closed__1, &l_Lean_Server_RpcEncodable_isOptField___closed__1_once, _init_l_Lean_Server_RpcEncodable_isOptField___closed__1);
v___x_10_ = lean_nat_dec_le(v___x_9_, v___x_8_);
if (v___x_10_ == 0)
{
lean_dec_ref(v___x_6_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_nat_sub(v___x_8_, v___x_9_);
v___x_13_ = lean_string_memcmp(v___x_6_, v___x_7_, v___x_12_, v___x_11_, v___x_9_);
lean_dec(v___x_12_);
lean_dec_ref(v___x_6_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_isOptField___boxed(lean_object* v_n_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Server_RpcEncodable_isOptField(v_n_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(size_t v_sz_17_, size_t v_i_18_, lean_object* v_bs_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_usize_dec_lt(v_i_18_, v_sz_17_);
if (v___x_20_ == 0)
{
return v_bs_19_;
}
else
{
lean_object* v_v_21_; lean_object* v___x_22_; lean_object* v_bs_x27_23_; size_t v___x_24_; size_t v___x_25_; lean_object* v___x_26_; 
v_v_21_ = lean_array_uget(v_bs_19_, v_i_18_);
v___x_22_ = lean_unsigned_to_nat(0u);
v_bs_x27_23_ = lean_array_uset(v_bs_19_, v_i_18_, v___x_22_);
v___x_24_ = ((size_t)1ULL);
v___x_25_ = lean_usize_add(v_i_18_, v___x_24_);
v___x_26_ = lean_array_uset(v_bs_x27_23_, v_i_18_, v_v_21_);
v_i_18_ = v___x_25_;
v_bs_19_ = v___x_26_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5___boxed(lean_object* v_sz_28_, lean_object* v_i_29_, lean_object* v_bs_30_){
_start:
{
size_t v_sz_boxed_31_; size_t v_i_boxed_32_; lean_object* v_res_33_; 
v_sz_boxed_31_ = lean_unbox_usize(v_sz_28_);
lean_dec(v_sz_28_);
v_i_boxed_32_ = lean_unbox_usize(v_i_29_);
lean_dec(v_i_29_);
v_res_33_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_boxed_31_, v_i_boxed_32_, v_bs_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(size_t v_sz_34_, size_t v_i_35_, lean_object* v_bs_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_usize_dec_lt(v_i_35_, v_sz_34_);
if (v___x_37_ == 0)
{
return v_bs_36_;
}
else
{
lean_object* v_v_38_; lean_object* v___x_39_; lean_object* v_bs_x27_40_; size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; 
v_v_38_ = lean_array_uget(v_bs_36_, v_i_35_);
v___x_39_ = lean_unsigned_to_nat(0u);
v_bs_x27_40_ = lean_array_uset(v_bs_36_, v_i_35_, v___x_39_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_add(v_i_35_, v___x_41_);
v___x_43_ = lean_array_uset(v_bs_x27_40_, v_i_35_, v_v_38_);
v_i_35_ = v___x_42_;
v_bs_36_ = v___x_43_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4___boxed(lean_object* v_sz_45_, lean_object* v_i_46_, lean_object* v_bs_47_){
_start:
{
size_t v_sz_boxed_48_; size_t v_i_boxed_49_; lean_object* v_res_50_; 
v_sz_boxed_48_ = lean_unbox_usize(v_sz_45_);
lean_dec(v_sz_45_);
v_i_boxed_49_ = lean_unbox_usize(v_i_46_);
lean_dec(v_i_46_);
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(v_sz_boxed_48_, v_i_boxed_49_, v_bs_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0(lean_object* v_msgData_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v_env_58_; lean_object* v___x_59_; lean_object* v_mctx_60_; lean_object* v_lctx_61_; lean_object* v_options_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = lean_st_ref_get(v___y_53_);
v_mctx_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_mctx_60_);
lean_dec(v___x_59_);
v_lctx_61_ = lean_ctor_get(v___y_52_, 2);
v_options_62_ = lean_ctor_get(v___y_54_, 2);
lean_inc_ref(v_options_62_);
lean_inc_ref(v_lctx_61_);
v___x_63_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_63_, 0, v_env_58_);
lean_ctor_set(v___x_63_, 1, v_mctx_60_);
lean_ctor_set(v___x_63_, 2, v_lctx_61_);
lean_ctor_set(v___x_63_, 3, v_options_62_);
v___x_64_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_msgData_51_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0___boxed(lean_object* v_msgData_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0(v_msgData_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_72_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_73_; double v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_float_of_nat(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(lean_object* v_cls_78_, lean_object* v_msg_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_131_; 
v_ref_85_ = lean_ctor_get(v___y_82_, 5);
v___x_86_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0(v_msg_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_131_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_131_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_131_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v_traceState_92_; lean_object* v_env_93_; lean_object* v_nextMacroScope_94_; lean_object* v_ngen_95_; lean_object* v_auxDeclNGen_96_; lean_object* v_cache_97_; lean_object* v_messages_98_; lean_object* v_infoState_99_; lean_object* v_snapshotTasks_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_130_; 
v___x_91_ = lean_st_ref_take(v___y_83_);
v_traceState_92_ = lean_ctor_get(v___x_91_, 4);
v_env_93_ = lean_ctor_get(v___x_91_, 0);
v_nextMacroScope_94_ = lean_ctor_get(v___x_91_, 1);
v_ngen_95_ = lean_ctor_get(v___x_91_, 2);
v_auxDeclNGen_96_ = lean_ctor_get(v___x_91_, 3);
v_cache_97_ = lean_ctor_get(v___x_91_, 5);
v_messages_98_ = lean_ctor_get(v___x_91_, 6);
v_infoState_99_ = lean_ctor_get(v___x_91_, 7);
v_snapshotTasks_100_ = lean_ctor_get(v___x_91_, 8);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_130_ == 0)
{
v___x_102_ = v___x_91_;
v_isShared_103_ = v_isSharedCheck_130_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_snapshotTasks_100_);
lean_inc(v_infoState_99_);
lean_inc(v_messages_98_);
lean_inc(v_cache_97_);
lean_inc(v_traceState_92_);
lean_inc(v_auxDeclNGen_96_);
lean_inc(v_ngen_95_);
lean_inc(v_nextMacroScope_94_);
lean_inc(v_env_93_);
lean_dec(v___x_91_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_130_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
uint64_t v_tid_104_; lean_object* v_traces_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_129_; 
v_tid_104_ = lean_ctor_get_uint64(v_traceState_92_, sizeof(void*)*1);
v_traces_105_ = lean_ctor_get(v_traceState_92_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v_traceState_92_);
if (v_isSharedCheck_129_ == 0)
{
v___x_107_ = v_traceState_92_;
v_isShared_108_ = v_isSharedCheck_129_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_traces_105_);
lean_dec(v_traceState_92_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_129_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; double v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_109_ = lean_box(0);
v___x_110_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0);
v___x_111_ = 0;
v___x_112_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1));
v___x_113_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_113_, 0, v_cls_78_);
lean_ctor_set(v___x_113_, 1, v___x_109_);
lean_ctor_set(v___x_113_, 2, v___x_112_);
lean_ctor_set_float(v___x_113_, sizeof(void*)*3, v___x_110_);
lean_ctor_set_float(v___x_113_, sizeof(void*)*3 + 8, v___x_110_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*3 + 16, v___x_111_);
v___x_114_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2));
v___x_115_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v_a_87_);
lean_ctor_set(v___x_115_, 2, v___x_114_);
lean_inc(v_ref_85_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_ref_85_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = l_Lean_PersistentArray_push___redArg(v_traces_105_, v___x_116_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_117_);
v___x_119_ = v___x_107_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_117_);
lean_ctor_set_uint64(v_reuseFailAlloc_128_, sizeof(void*)*1, v_tid_104_);
v___x_119_ = v_reuseFailAlloc_128_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 4, v___x_119_);
v___x_121_ = v___x_102_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_env_93_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_nextMacroScope_94_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_ngen_95_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_auxDeclNGen_96_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_127_, 5, v_cache_97_);
lean_ctor_set(v_reuseFailAlloc_127_, 6, v_messages_98_);
lean_ctor_set(v_reuseFailAlloc_127_, 7, v_infoState_99_);
lean_ctor_set(v_reuseFailAlloc_127_, 8, v_snapshotTasks_100_);
v___x_121_ = v_reuseFailAlloc_127_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_122_ = lean_st_ref_set(v___y_83_, v___x_121_);
v___x_123_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_123_);
v___x_125_ = v___x_89_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___boxed(lean_object* v_cls_132_, lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v_cls_132_, v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(lean_object* v___x_168_, lean_object* v___x_169_, lean_object* v___x_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_bs_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_usize_dec_lt(v_i_172_, v_sz_171_);
if (v___x_174_ == 0)
{
lean_dec(v___x_170_);
lean_dec(v___x_169_);
lean_dec(v___x_168_);
return v_bs_173_;
}
else
{
lean_object* v_v_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_204_; 
v_v_175_ = lean_array_uget(v_bs_173_, v_i_172_);
v_fst_176_ = lean_ctor_get(v_v_175_, 0);
v_snd_177_ = lean_ctor_get(v_v_175_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_v_175_);
if (v_isSharedCheck_204_ == 0)
{
v___x_179_ = v_v_175_;
v_isShared_180_ = v_isSharedCheck_204_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_snd_177_);
lean_inc(v_fst_176_);
lean_dec(v_v_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_204_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_bs_x27_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_183_ = lean_unsigned_to_nat(0u);
v_bs_x27_184_ = lean_array_uset(v_bs_173_, v_i_172_, v___x_183_);
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8));
v___x_186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc(v___x_168_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 2);
lean_ctor_set(v___x_179_, 1, v___x_186_);
lean_ctor_set(v___x_179_, 0, v___x_168_);
v___x_188_ = v___x_179_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_203_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
lean_inc_n(v___x_168_, 7);
v___x_189_ = l_Lean_Syntax_node1(v___x_168_, v___x_181_, v_fst_176_);
v___x_190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_168_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_Syntax_node2(v___x_168_, v___x_190_, v___x_192_, v_snd_177_);
v___x_194_ = l_Lean_Syntax_node1(v___x_168_, v___x_181_, v___x_193_);
lean_inc_n(v___x_169_, 2);
v___x_195_ = l_Lean_Syntax_node2(v___x_168_, v___x_182_, v___x_169_, v___x_194_);
v___x_196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_168_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
lean_inc(v___x_170_);
v___x_198_ = l_Lean_Syntax_node6(v___x_168_, v___x_185_, v___x_170_, v___x_188_, v___x_189_, v___x_195_, v___x_169_, v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_172_, v___x_199_);
v___x_201_ = lean_array_uset(v_bs_x27_184_, v_i_172_, v___x_198_);
v_i_172_ = v___x_200_;
v_bs_173_ = v___x_201_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___boxed(lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v_sz_208_, lean_object* v_i_209_, lean_object* v_bs_210_){
_start:
{
size_t v_sz_boxed_211_; size_t v_i_boxed_212_; lean_object* v_res_213_; 
v_sz_boxed_211_ = lean_unbox_usize(v_sz_208_);
lean_dec(v_sz_208_);
v_i_boxed_212_ = lean_unbox_usize(v_i_209_);
lean_dec(v_i_209_);
v_res_213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(v___x_205_, v___x_206_, v___x_207_, v_sz_boxed_211_, v_i_boxed_212_, v_bs_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
if (lean_obj_tag(v_a_214_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = l_List_reverse___redArg(v_a_215_);
return v___x_216_;
}
else
{
lean_object* v_head_217_; lean_object* v_tail_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_227_; 
v_head_217_ = lean_ctor_get(v_a_214_, 0);
v_tail_218_ = lean_ctor_get(v_a_214_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_227_ == 0)
{
v___x_220_ = v_a_214_;
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_tail_218_);
lean_inc(v_head_217_);
lean_dec(v_a_214_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_MessageData_ofExpr(v_head_217_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_a_215_);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_a_215_);
v___x_224_ = v_reuseFailAlloc_226_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
v_a_214_ = v_tail_218_;
v_a_215_ = v___x_224_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(size_t v_sz_228_, size_t v_i_229_, lean_object* v_bs_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = lean_usize_dec_lt(v_i_229_, v_sz_228_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v_bs_230_);
return v___x_236_;
}
else
{
lean_object* v_v_237_; lean_object* v___x_238_; 
v_v_237_ = lean_array_uget_borrowed(v_bs_230_, v_i_229_);
v___x_238_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_v_237_, v___y_231_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v_bs_x27_241_; lean_object* v___x_242_; lean_object* v___x_243_; size_t v___x_244_; size_t v___x_245_; lean_object* v___x_246_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref(v___x_238_);
v___x_240_ = lean_unsigned_to_nat(0u);
v_bs_x27_241_ = lean_array_uset(v_bs_230_, v_i_229_, v___x_240_);
v___x_242_ = l_Lean_LocalDecl_userName(v_a_239_);
lean_dec(v_a_239_);
v___x_243_ = lean_mk_syntax_ident(v___x_242_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_229_, v___x_244_);
v___x_246_ = lean_array_uset(v_bs_x27_241_, v_i_229_, v___x_243_);
v_i_229_ = v___x_245_;
v_bs_230_ = v___x_246_;
goto _start;
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v_bs_230_);
v_a_248_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_238_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_238_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg___boxed(lean_object* v_sz_256_, lean_object* v_i_257_, lean_object* v_bs_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
size_t v_sz_boxed_263_; size_t v_i_boxed_264_; lean_object* v_res_265_; 
v_sz_boxed_263_ = lean_unbox_usize(v_sz_256_);
lean_dec(v_sz_256_);
v_i_boxed_264_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_boxed_263_, v_i_boxed_264_, v_bs_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(uint8_t v___x_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_ref_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_ref_274_ = lean_ctor_get(v___y_271_, 5);
v___x_275_ = l_Lean_SourceInfo_fromRef(v_ref_274_, v___x_266_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1___boxed(lean_object* v___x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
uint8_t v___x_31146__boxed_285_; lean_object* v_res_286_; 
v___x_31146__boxed_285_ = lean_unbox(v___x_277_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(v___x_31146__boxed_285_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_ref_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_ref_294_ = lean_ctor_get(v___y_291_, 5);
v___x_295_ = 0;
v___x_296_ = l_Lean_SourceInfo_fromRef(v_ref_294_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0___boxed(lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_305_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2(lean_object* v_opts_306_, lean_object* v_opt_307_){
_start:
{
lean_object* v_name_308_; lean_object* v_defValue_309_; lean_object* v_map_310_; lean_object* v___x_311_; 
v_name_308_ = lean_ctor_get(v_opt_307_, 0);
v_defValue_309_ = lean_ctor_get(v_opt_307_, 1);
v_map_310_ = lean_ctor_get(v_opts_306_, 0);
v___x_311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_310_, v_name_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = lean_unbox(v_defValue_309_);
return v___x_312_;
}
else
{
lean_object* v_val_313_; 
v_val_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_313_);
lean_dec_ref(v___x_311_);
if (lean_obj_tag(v_val_313_) == 1)
{
uint8_t v_v_314_; 
v_v_314_ = lean_ctor_get_uint8(v_val_313_, 0);
lean_dec_ref(v_val_313_);
return v_v_314_;
}
else
{
uint8_t v___x_315_; 
lean_dec(v_val_313_);
v___x_315_ = lean_unbox(v_defValue_309_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_316_, lean_object* v_opt_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2(v_opts_316_, v_opt_317_);
lean_dec_ref(v_opt_317_);
lean_dec_ref(v_opts_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_box(1);
v___x_321_ = l_Lean_MessageData_ofFormat(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__2));
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
return v_x_327_;
}
else
{
lean_object* v_head_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_352_; 
v_head_329_ = lean_ctor_get(v_x_328_, 0);
v_tail_330_ = lean_ctor_get(v_x_328_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_352_ == 0)
{
v___x_332_ = v_x_328_;
v_isShared_333_ = v_isSharedCheck_352_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_head_329_);
lean_dec(v_x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_352_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_before_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_350_; 
v_before_334_ = lean_ctor_get(v_head_329_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_head_329_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_head_329_, 1);
lean_dec(v_unused_351_);
v___x_336_ = v_head_329_;
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_before_334_);
lean_dec(v_head_329_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_350_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 7);
lean_ctor_set(v___x_336_, 1, v___x_338_);
lean_ctor_set(v___x_336_, 0, v_x_327_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_x_327_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_349_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 7);
lean_ctor_set(v___x_332_, 1, v___x_341_);
lean_ctor_set(v___x_332_, 0, v___x_340_);
v___x_343_ = v___x_332_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_348_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_MessageData_ofSyntax(v_before_334_);
v___x_345_ = l_Lean_indentD(v___x_344_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_343_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v_x_327_ = v___x_346_;
v_x_328_ = v_tail_330_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__1));
v___x_357_ = l_Lean_MessageData_ofFormat(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg(lean_object* v_msgData_358_, lean_object* v_macroStack_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_options_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_options_362_ = lean_ctor_get(v___y_360_, 2);
v___x_363_ = l_Lean_Elab_pp_macroStack;
v___x_364_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2(v_options_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v_macroStack_359_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_msgData_358_);
return v___x_365_;
}
else
{
if (lean_obj_tag(v_macroStack_359_) == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_msgData_358_);
return v___x_366_;
}
else
{
lean_object* v_head_367_; lean_object* v_after_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_383_; 
v_head_367_ = lean_ctor_get(v_macroStack_359_, 0);
lean_inc(v_head_367_);
v_after_368_ = lean_ctor_get(v_head_367_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_head_367_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_head_367_, 0);
lean_dec(v_unused_384_);
v___x_370_ = v_head_367_;
v_isShared_371_ = v_isSharedCheck_383_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_after_368_);
lean_dec(v_head_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_383_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 7);
lean_ctor_set(v___x_370_, 1, v___x_372_);
lean_ctor_set(v___x_370_, 0, v_msgData_358_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_msgData_358_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_382_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_msgData_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_375_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_MessageData_ofSyntax(v_after_368_);
v___x_378_ = l_Lean_indentD(v___x_377_);
v_msgData_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_379_, 0, v___x_376_);
lean_ctor_set(v_msgData_379_, 1, v___x_378_);
v___x_380_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3(v_msgData_379_, v_macroStack_359_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_385_, lean_object* v_macroStack_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg(v_msgData_385_, v_macroStack_386_, v___y_387_);
lean_dec_ref(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_ref_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v_macroStack_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_ref_398_ = lean_ctor_get(v___y_395_, 5);
v___x_399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0(v_msg_390_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_399_);
v_macroStack_401_ = lean_ctor_get(v___y_391_, 1);
lean_inc_n(v_macroStack_401_, 2);
v___x_402_ = l_Lean_Elab_getBetterRef(v_ref_398_, v_macroStack_401_);
v___x_403_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg(v_a_400_, v_macroStack_401_, v___y_395_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_402_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___boxed(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_421_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2));
v___x_426_ = l_String_toRawSubstring_x27(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Array_mkArray0(lean_box(0));
return v___x_447_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20));
v___x_470_ = l_String_toRawSubstring_x27(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29));
v___x_493_ = l_String_toRawSubstring_x27(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36));
v___x_507_ = l_String_toRawSubstring_x27(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42));
v___x_523_ = l_String_toRawSubstring_x27(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1));
v___x_556_ = l_String_toRawSubstring_x27(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76));
v___x_612_ = l_String_toRawSubstring_x27(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81));
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(lean_object* v_as_621_, size_t v_sz_622_, size_t v_i_623_, lean_object* v_b_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_a_633_; uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_lt(v_i_623_, v_sz_622_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_b_624_);
return v___x_638_;
}
else
{
lean_object* v_snd_639_; lean_object* v_snd_640_; lean_object* v_fst_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_900_; 
v_snd_639_ = lean_ctor_get(v_b_624_, 1);
lean_inc(v_snd_639_);
v_snd_640_ = lean_ctor_get(v_snd_639_, 1);
lean_inc(v_snd_640_);
v_fst_641_ = lean_ctor_get(v_b_624_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_b_624_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_b_624_, 1);
lean_dec(v_unused_901_);
v___x_643_ = v_b_624_;
v_isShared_644_ = v_isSharedCheck_900_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_fst_641_);
lean_dec(v_b_624_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_900_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_fst_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_898_; 
v_fst_645_ = lean_ctor_get(v_snd_639_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_snd_639_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_snd_639_, 1);
lean_dec(v_unused_899_);
v___x_647_ = v_snd_639_;
v_isShared_648_ = v_isSharedCheck_898_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_fst_645_);
lean_dec(v_snd_639_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_898_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_897_; 
v_fst_649_ = lean_ctor_get(v_snd_640_, 0);
v_snd_650_ = lean_ctor_get(v_snd_640_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_snd_640_);
if (v_isSharedCheck_897_ == 0)
{
v___x_652_ = v_snd_640_;
v_isShared_653_ = v_isSharedCheck_897_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snd_650_);
lean_inc(v_fst_649_);
lean_dec(v_snd_640_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_897_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_a_654_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_a_654_ = lean_array_uget_borrowed(v_as_621_, v_i_623_);
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80));
v___x_886_ = lean_name_eq(v_a_654_, v___x_885_);
if (v___x_886_ == 0)
{
v___y_656_ = v___y_625_;
v___y_657_ = v___y_626_;
v___y_658_ = v___y_627_;
v___y_659_ = v___y_628_;
v___y_660_ = v___y_629_;
v___y_661_ = v___y_630_;
goto v___jp_655_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82);
v___x_888_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_887_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_dec_ref(v___x_888_);
v___y_656_ = v___y_625_;
v___y_657_ = v___y_626_;
v___y_658_ = v___y_627_;
v___y_659_ = v___y_628_;
v___y_660_ = v___y_629_;
v___y_661_ = v___y_630_;
goto v___jp_655_;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_652_);
lean_dec(v_snd_650_);
lean_dec(v_fst_649_);
lean_del_object(v___x_647_);
lean_dec(v_fst_645_);
lean_del_object(v___x_643_);
lean_dec(v_fst_641_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
v___jp_655_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
lean_inc_n(v_a_654_, 2);
v___x_662_ = lean_mk_syntax_ident(v_a_654_);
lean_inc(v___x_662_);
v___x_663_ = lean_array_push(v_fst_641_, v___x_662_);
v___x_664_ = l_Lean_Server_RpcEncodable_isOptField(v_a_654_);
if (v___x_664_ == 0)
{
lean_object* v_ref_665_; lean_object* v_quotContext_666_; lean_object* v_currMacroScope_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_ref_665_ = lean_ctor_get(v___y_660_, 5);
v_quotContext_666_ = lean_ctor_get(v___y_660_, 10);
v_currMacroScope_667_ = lean_ctor_get(v___y_660_, 11);
v___x_668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(v___x_664_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_n(v_a_670_, 14);
lean_dec_ref(v___x_669_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4));
v___x_672_ = lean_box(0);
v___x_673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v_a_670_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
lean_inc_ref_n(v___x_677_, 3);
lean_inc_n(v___x_662_, 2);
v___x_678_ = l_Lean_Syntax_node2(v_a_670_, v___x_674_, v___x_662_, v___x_677_);
v___x_679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v_a_670_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v_a_670_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_686_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21);
v___x_687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
lean_inc_n(v_currMacroScope_667_, 2);
lean_inc_n(v_quotContext_666_, 2);
v___x_688_ = l_Lean_addMacroScope(v_quotContext_666_, v___x_687_, v_currMacroScope_667_);
v___x_689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26));
v___x_690_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_690_, 0, v_a_670_);
lean_ctor_set(v___x_690_, 1, v___x_686_);
lean_ctor_set(v___x_690_, 2, v___x_688_);
lean_ctor_set(v___x_690_, 3, v___x_689_);
v___x_691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
v___x_692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30);
v___x_693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
v___x_694_ = l_Lean_addMacroScope(v_quotContext_666_, v___x_693_, v_currMacroScope_667_);
lean_inc(v___x_694_);
v___x_695_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_695_, 0, v_a_670_);
lean_ctor_set(v___x_695_, 1, v___x_692_);
lean_ctor_set(v___x_695_, 2, v___x_694_);
lean_ctor_set(v___x_695_, 3, v___x_672_);
v___x_696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_670_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_Syntax_node3(v_a_670_, v___x_691_, v___x_695_, v___x_697_, v___x_662_);
v___x_699_ = l_Lean_Syntax_node1(v_a_670_, v___x_675_, v___x_698_);
v___x_700_ = l_Lean_Syntax_node2(v_a_670_, v___x_685_, v___x_690_, v___x_699_);
v___x_701_ = l_Lean_Syntax_node2(v_a_670_, v___x_682_, v___x_684_, v___x_700_);
v___x_702_ = l_Lean_Syntax_node3(v_a_670_, v___x_679_, v___x_681_, v___x_677_, v___x_701_);
v___x_703_ = l_Lean_Syntax_node3(v_a_670_, v___x_675_, v___x_677_, v___x_677_, v___x_702_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(v___x_664_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_n(v_a_705_, 14);
lean_dec_ref(v___x_704_);
v___x_706_ = l_Lean_SourceInfo_fromRef(v_ref_665_, v___x_664_);
lean_inc_n(v_currMacroScope_667_, 2);
lean_inc_n(v_quotContext_666_, 2);
v___x_707_ = l_Lean_addMacroScope(v_quotContext_666_, v___x_671_, v_currMacroScope_667_);
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35));
v___x_709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_709_, 0, v___x_706_);
lean_ctor_set(v___x_709_, 1, v___x_668_);
lean_ctor_set(v___x_709_, 2, v___x_707_);
lean_ctor_set(v___x_709_, 3, v___x_708_);
v___x_710_ = lean_array_push(v_fst_645_, v___x_709_);
v___x_711_ = l_Lean_Syntax_node2(v_a_670_, v___x_673_, v___x_678_, v___x_703_);
v___x_712_ = lean_array_push(v_fst_649_, v___x_711_);
v___x_713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_713_, 0, v_a_705_);
lean_ctor_set(v___x_713_, 1, v___x_675_);
lean_ctor_set(v___x_713_, 2, v___x_676_);
lean_inc_ref_n(v___x_713_, 3);
lean_inc(v___x_662_);
v___x_714_ = l_Lean_Syntax_node2(v_a_705_, v___x_674_, v___x_662_, v___x_713_);
v___x_715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_715_, 0, v_a_705_);
lean_ctor_set(v___x_715_, 1, v___x_680_);
v___x_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_716_, 0, v_a_705_);
lean_ctor_set(v___x_716_, 1, v___x_683_);
v___x_717_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37);
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
v___x_719_ = l_Lean_addMacroScope(v_quotContext_666_, v___x_718_, v_currMacroScope_667_);
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41));
v___x_721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_721_, 0, v_a_705_);
lean_ctor_set(v___x_721_, 1, v___x_717_);
lean_ctor_set(v___x_721_, 2, v___x_719_);
lean_ctor_set(v___x_721_, 3, v___x_720_);
v___x_722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_722_, 0, v_a_705_);
lean_ctor_set(v___x_722_, 1, v___x_692_);
lean_ctor_set(v___x_722_, 2, v___x_694_);
lean_ctor_set(v___x_722_, 3, v___x_672_);
v___x_723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_723_, 0, v_a_705_);
lean_ctor_set(v___x_723_, 1, v___x_696_);
v___x_724_ = l_Lean_Syntax_node3(v_a_705_, v___x_691_, v___x_722_, v___x_723_, v___x_662_);
v___x_725_ = l_Lean_Syntax_node1(v_a_705_, v___x_675_, v___x_724_);
v___x_726_ = l_Lean_Syntax_node2(v_a_705_, v___x_685_, v___x_721_, v___x_725_);
v___x_727_ = l_Lean_Syntax_node2(v_a_705_, v___x_682_, v___x_716_, v___x_726_);
v___x_728_ = l_Lean_Syntax_node3(v_a_705_, v___x_679_, v___x_715_, v___x_713_, v___x_727_);
v___x_729_ = l_Lean_Syntax_node3(v_a_705_, v___x_675_, v___x_713_, v___x_713_, v___x_728_);
v___x_730_ = l_Lean_Syntax_node2(v_a_705_, v___x_673_, v___x_714_, v___x_729_);
v___x_731_ = lean_array_push(v_snd_650_, v___x_730_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_731_);
lean_ctor_set(v___x_652_, 0, v___x_712_);
v___x_733_ = v___x_652_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_740_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_733_);
lean_ctor_set(v___x_647_, 0, v___x_710_);
v___x_735_ = v___x_647_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_735_);
lean_ctor_set(v___x_643_, 0, v___x_663_);
v___x_737_ = v___x_643_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
v_a_633_ = v___x_737_;
goto v___jp_632_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_703_);
lean_dec(v___x_694_);
lean_dec(v___x_678_);
lean_dec(v_a_670_);
lean_dec_ref(v___x_663_);
lean_dec(v___x_662_);
lean_del_object(v___x_652_);
lean_dec(v_snd_650_);
lean_dec(v_fst_649_);
lean_del_object(v___x_647_);
lean_dec(v_fst_645_);
lean_del_object(v___x_643_);
v_a_741_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_704_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_704_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v___x_663_);
lean_dec(v___x_662_);
lean_del_object(v___x_652_);
lean_dec(v_snd_650_);
lean_dec(v_fst_649_);
lean_del_object(v___x_647_);
lean_dec(v_fst_645_);
lean_del_object(v___x_643_);
v_a_749_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_669_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_669_);
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
else
{
lean_object* v_ref_757_; lean_object* v_quotContext_758_; lean_object* v_currMacroScope_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_ref_757_ = lean_ctor_get(v___y_660_, 5);
v_quotContext_758_ = lean_ctor_get(v___y_660_, 10);
v_currMacroScope_759_ = lean_ctor_get(v___y_660_, 11);
v___x_760_ = 0;
v___x_761_ = l_Lean_SourceInfo_fromRef(v_ref_757_, v___x_760_);
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_763_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44));
lean_inc(v_currMacroScope_759_);
lean_inc(v_quotContext_758_);
v___x_765_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_764_, v_currMacroScope_759_);
v___x_766_ = lean_box(0);
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49));
lean_inc(v___x_761_);
v___x_768_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_768_, 0, v___x_761_);
lean_ctor_set(v___x_768_, 1, v___x_763_);
lean_ctor_set(v___x_768_, 2, v___x_765_);
lean_ctor_set(v___x_768_, 3, v___x_767_);
v___x_769_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3);
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4));
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 22);
lean_dec_ref(v___x_771_);
lean_inc_n(v_currMacroScope_759_, 5);
lean_inc_n(v_quotContext_758_, 5);
v___x_773_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_770_, v_currMacroScope_759_);
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35));
lean_inc_n(v___x_761_, 2);
v___x_775_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_775_, 0, v___x_761_);
lean_ctor_set(v___x_775_, 1, v___x_769_);
lean_ctor_set(v___x_775_, 2, v___x_773_);
lean_ctor_set(v___x_775_, 3, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_777_ = l_Lean_Syntax_node1(v___x_761_, v___x_776_, v___x_775_);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_781_, 0, v_a_772_);
lean_ctor_set(v___x_781_, 1, v___x_776_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_inc_ref_n(v___x_781_, 3);
lean_inc_n(v___x_662_, 2);
v___x_782_ = l_Lean_Syntax_node2(v_a_772_, v___x_779_, v___x_662_, v___x_781_);
v___x_783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_772_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_772_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_772_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
v___x_795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56);
v___x_796_ = lean_box(0);
v___x_797_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_796_, v_currMacroScope_759_);
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75));
lean_inc(v___x_797_);
v___x_799_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_799_, 0, v_a_772_);
lean_ctor_set(v___x_799_, 1, v___x_795_);
lean_ctor_set(v___x_799_, 2, v___x_797_);
lean_ctor_set(v___x_799_, 3, v___x_798_);
v___x_800_ = l_Lean_Syntax_node1(v_a_772_, v___x_794_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node2(v_a_772_, v___x_791_, v___x_793_, v___x_800_);
v___x_802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30);
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
v___x_804_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_803_, v_currMacroScope_759_);
lean_inc(v___x_804_);
v___x_805_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_805_, 0, v_a_772_);
lean_ctor_set(v___x_805_, 1, v___x_802_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
lean_ctor_set(v___x_805_, 3, v___x_766_);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32));
v___x_807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_772_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
lean_inc_ref(v___x_807_);
v___x_808_ = l_Lean_Syntax_node3(v_a_772_, v___x_789_, v___x_805_, v___x_807_, v___x_662_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_810_, 0, v_a_772_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_Syntax_node3(v_a_772_, v___x_790_, v___x_801_, v___x_808_, v___x_810_);
v___x_812_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78));
v___x_814_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_813_, v_currMacroScope_759_);
lean_inc(v___x_814_);
v___x_815_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_815_, 0, v_a_772_);
lean_ctor_set(v___x_815_, 1, v___x_812_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
lean_ctor_set(v___x_815_, 3, v___x_766_);
v___x_816_ = l_Lean_Syntax_node3(v_a_772_, v___x_789_, v___x_811_, v___x_807_, v___x_815_);
v___x_817_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21);
v___x_818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
v___x_819_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_818_, v_currMacroScope_759_);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26));
v___x_821_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_821_, 0, v_a_772_);
lean_ctor_set(v___x_821_, 1, v___x_817_);
lean_ctor_set(v___x_821_, 2, v___x_819_);
lean_ctor_set(v___x_821_, 3, v___x_820_);
v___x_822_ = l_Lean_Syntax_node1(v_a_772_, v___x_776_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node2(v_a_772_, v___x_762_, v___x_816_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node2(v_a_772_, v___x_786_, v___x_788_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node3(v_a_772_, v___x_783_, v___x_785_, v___x_781_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node3(v_a_772_, v___x_776_, v___x_781_, v___x_781_, v___x_825_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_n(v_a_828_, 22);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Lean_Syntax_node2(v___x_761_, v___x_762_, v___x_768_, v___x_777_);
v___x_830_ = lean_array_push(v_fst_645_, v___x_829_);
v___x_831_ = l_Lean_Syntax_node2(v_a_772_, v___x_778_, v___x_782_, v___x_826_);
v___x_832_ = lean_array_push(v_fst_649_, v___x_831_);
v___x_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_833_, 0, v_a_828_);
lean_ctor_set(v___x_833_, 1, v___x_776_);
lean_ctor_set(v___x_833_, 2, v___x_780_);
lean_inc_ref_n(v___x_833_, 3);
lean_inc(v___x_662_);
v___x_834_ = l_Lean_Syntax_node2(v_a_828_, v___x_779_, v___x_662_, v___x_833_);
v___x_835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_835_, 0, v_a_828_);
lean_ctor_set(v___x_835_, 1, v___x_784_);
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v_a_828_);
lean_ctor_set(v___x_836_, 1, v___x_787_);
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v_a_828_);
lean_ctor_set(v___x_837_, 1, v___x_792_);
v___x_838_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_838_, 0, v_a_828_);
lean_ctor_set(v___x_838_, 1, v___x_795_);
lean_ctor_set(v___x_838_, 2, v___x_797_);
lean_ctor_set(v___x_838_, 3, v___x_798_);
v___x_839_ = l_Lean_Syntax_node1(v_a_828_, v___x_794_, v___x_838_);
v___x_840_ = l_Lean_Syntax_node2(v_a_828_, v___x_791_, v___x_837_, v___x_839_);
v___x_841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_841_, 0, v_a_828_);
lean_ctor_set(v___x_841_, 1, v___x_802_);
lean_ctor_set(v___x_841_, 2, v___x_804_);
lean_ctor_set(v___x_841_, 3, v___x_766_);
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v_a_828_);
lean_ctor_set(v___x_842_, 1, v___x_806_);
lean_inc_ref(v___x_842_);
v___x_843_ = l_Lean_Syntax_node3(v_a_828_, v___x_789_, v___x_841_, v___x_842_, v___x_662_);
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v_a_828_);
lean_ctor_set(v___x_844_, 1, v___x_809_);
v___x_845_ = l_Lean_Syntax_node3(v_a_828_, v___x_790_, v___x_840_, v___x_843_, v___x_844_);
v___x_846_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_846_, 0, v_a_828_);
lean_ctor_set(v___x_846_, 1, v___x_812_);
lean_ctor_set(v___x_846_, 2, v___x_814_);
lean_ctor_set(v___x_846_, 3, v___x_766_);
v___x_847_ = l_Lean_Syntax_node3(v_a_828_, v___x_789_, v___x_845_, v___x_842_, v___x_846_);
v___x_848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
lean_inc(v_currMacroScope_759_);
lean_inc(v_quotContext_758_);
v___x_850_ = l_Lean_addMacroScope(v_quotContext_758_, v___x_849_, v_currMacroScope_759_);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41));
v___x_852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_852_, 0, v_a_828_);
lean_ctor_set(v___x_852_, 1, v___x_848_);
lean_ctor_set(v___x_852_, 2, v___x_850_);
lean_ctor_set(v___x_852_, 3, v___x_851_);
v___x_853_ = l_Lean_Syntax_node1(v_a_828_, v___x_776_, v___x_852_);
v___x_854_ = l_Lean_Syntax_node2(v_a_828_, v___x_762_, v___x_847_, v___x_853_);
v___x_855_ = l_Lean_Syntax_node2(v_a_828_, v___x_786_, v___x_836_, v___x_854_);
v___x_856_ = l_Lean_Syntax_node3(v_a_828_, v___x_783_, v___x_835_, v___x_833_, v___x_855_);
v___x_857_ = l_Lean_Syntax_node3(v_a_828_, v___x_776_, v___x_833_, v___x_833_, v___x_856_);
v___x_858_ = l_Lean_Syntax_node2(v_a_828_, v___x_778_, v___x_834_, v___x_857_);
v___x_859_ = lean_array_push(v_snd_650_, v___x_858_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_859_);
lean_ctor_set(v___x_652_, 0, v___x_832_);
v___x_861_ = v___x_652_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_868_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_861_);
lean_ctor_set(v___x_647_, 0, v___x_830_);
v___x_863_ = v___x_647_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_861_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_863_);
lean_ctor_set(v___x_643_, 0, v___x_663_);
v___x_865_ = v___x_643_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
v_a_633_ = v___x_865_;
goto v___jp_632_;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v___x_826_);
lean_dec(v___x_814_);
lean_dec(v___x_804_);
lean_dec(v___x_797_);
lean_dec(v___x_782_);
lean_dec(v___x_777_);
lean_dec(v_a_772_);
lean_dec_ref(v___x_768_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_663_);
lean_dec(v___x_662_);
lean_del_object(v___x_652_);
lean_dec(v_snd_650_);
lean_dec(v_fst_649_);
lean_del_object(v___x_647_);
lean_dec(v_fst_645_);
lean_del_object(v___x_643_);
v_a_869_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_827_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_827_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___x_768_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_663_);
lean_dec(v___x_662_);
lean_del_object(v___x_652_);
lean_dec(v_snd_650_);
lean_dec(v_fst_649_);
lean_del_object(v___x_647_);
lean_dec(v_fst_645_);
lean_del_object(v___x_643_);
v_a_877_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_771_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_771_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
}
}
v___jp_632_:
{
size_t v___x_634_; size_t v___x_635_; 
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_623_, v___x_634_);
v_i_623_ = v___x_635_;
v_b_624_ = v_a_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___boxed(lean_object* v_as_902_, lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
size_t v_sz_boxed_913_; size_t v_i_boxed_914_; lean_object* v_res_915_; 
v_sz_boxed_913_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_914_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(v_as_902_, v_sz_boxed_913_, v_i_boxed_914_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec_ref(v_as_902_);
return v_res_915_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14));
v___x_958_ = l_String_toRawSubstring_x27(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25));
v___x_983_ = l_String_toRawSubstring_x27(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34));
v___x_1003_ = l_String_toRawSubstring_x27(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0));
v___x_1051_ = l_String_toRawSubstring_x27(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75));
v___x_1115_ = l_String_toRawSubstring_x27(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80));
v___x_1126_ = l_String_toRawSubstring_x27(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102));
v___x_1182_ = l_String_toRawSubstring_x27(v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33));
v___x_1196_ = l_Lean_mkAtom(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109));
v___x_1199_ = l_String_toRawSubstring_x27(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127));
v___x_1247_ = l_String_toRawSubstring_x27(v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136));
v___x_1275_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138));
v___x_1276_ = l_Lean_Name_append(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(lean_object* v_indVal_1283_, lean_object* v_params_1284_, lean_object* v_encInstBinders_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_toConstantVal_1294_; lean_object* v_options_1295_; lean_object* v_env_1296_; lean_object* v_name_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1638_; 
v___x_1293_ = lean_st_ref_get(v_a_1291_);
v_toConstantVal_1294_ = lean_ctor_get(v_indVal_1283_, 0);
lean_inc_ref(v_toConstantVal_1294_);
lean_dec_ref(v_indVal_1283_);
v_options_1295_ = lean_ctor_get(v_a_1290_, 2);
v_env_1296_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_ref(v_env_1296_);
lean_dec(v___x_1293_);
v_name_1297_ = lean_ctor_get(v_toConstantVal_1294_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_toConstantVal_1294_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; lean_object* v_unused_1640_; 
v_unused_1639_ = lean_ctor_get(v_toConstantVal_1294_, 2);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_toConstantVal_1294_, 1);
lean_dec(v_unused_1640_);
v___x_1299_ = v_toConstantVal_1294_;
v_isShared_1300_ = v_isSharedCheck_1638_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_name_1297_);
lean_dec(v_toConstantVal_1294_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1638_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_inheritedTraceOptions_1301_; uint8_t v_hasTrace_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; 
v_inheritedTraceOptions_1301_ = lean_ctor_get(v_a_1290_, 13);
v_hasTrace_1302_ = lean_ctor_get_uint8(v_options_1295_, sizeof(void*)*1);
v___x_1303_ = 0;
lean_inc(v_name_1297_);
v___x_1304_ = l_Lean_getStructureFieldsFlattened(v_env_1296_, v_name_1297_, v___x_1303_);
if (v_hasTrace_1302_ == 0)
{
v___y_1306_ = v_a_1286_;
v___y_1307_ = v_a_1287_;
v___y_1308_ = v_a_1288_;
v___y_1309_ = v_a_1289_;
v___y_1310_ = v_a_1290_;
v___y_1311_ = v_a_1291_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136));
v___x_1617_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139);
v___x_1618_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1301_, v_options_1295_, v___x_1617_);
if (v___x_1618_ == 0)
{
v___y_1306_ = v_a_1286_;
v___y_1307_ = v_a_1287_;
v___y_1308_ = v_a_1288_;
v___y_1309_ = v_a_1289_;
v___y_1310_ = v_a_1290_;
v___y_1311_ = v_a_1291_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1619_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141);
lean_inc(v_name_1297_);
v___x_1620_ = l_Lean_MessageData_ofName(v_name_1297_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
lean_inc_ref(v_params_1284_);
v___x_1624_ = lean_array_to_list(v_params_1284_);
v___x_1625_ = lean_box(0);
v___x_1626_ = l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(v___x_1624_, v___x_1625_);
v___x_1627_ = l_Lean_MessageData_ofList(v___x_1626_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1623_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v___x_1616_, v___x_1628_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref(v___x_1629_);
v___y_1306_ = v_a_1286_;
v___y_1307_ = v_a_1287_;
v___y_1308_ = v_a_1288_;
v___y_1309_ = v_a_1289_;
v___y_1310_ = v_a_1290_;
v___y_1311_ = v_a_1291_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___x_1304_);
lean_del_object(v___x_1299_);
lean_dec(v_name_1297_);
lean_dec_ref(v_params_1284_);
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
v___jp_1305_:
{
lean_object* v___x_1312_; size_t v_sz_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3));
v_sz_1313_ = lean_array_size(v___x_1304_);
v___x_1314_ = ((size_t)0ULL);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(v___x_1304_, v_sz_1313_, v___x_1314_, v___x_1312_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec_ref(v___x_1304_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; size_t v_sz_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1315_);
v_sz_1317_ = lean_array_size(v_params_1284_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_1317_, v___x_1314_, v_params_1284_, v___y_1308_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_snd_1319_; lean_object* v_snd_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1599_; 
v_snd_1319_ = lean_ctor_get(v_a_1316_, 1);
lean_inc(v_snd_1319_);
v_snd_1320_ = lean_ctor_get(v_snd_1319_, 1);
lean_inc(v_snd_1320_);
v_a_1321_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1323_ = v___x_1318_;
v_isShared_1324_ = v_isSharedCheck_1599_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1599_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_fst_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1597_; 
v_fst_1325_ = lean_ctor_get(v_a_1316_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_a_1316_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_a_1316_, 1);
lean_dec(v_unused_1598_);
v___x_1327_ = v_a_1316_;
v_isShared_1328_ = v_isSharedCheck_1597_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_fst_1325_);
lean_dec(v_a_1316_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1597_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_fst_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1595_; 
v_fst_1329_ = lean_ctor_get(v_snd_1319_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_snd_1319_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v_snd_1319_, 1);
lean_dec(v_unused_1596_);
v___x_1331_ = v_snd_1319_;
v_isShared_1332_ = v_isSharedCheck_1595_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_fst_1329_);
lean_dec(v_snd_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1595_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1594_; 
v_fst_1333_ = lean_ctor_get(v_snd_1320_, 0);
v_snd_1334_ = lean_ctor_get(v_snd_1320_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_snd_1320_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1336_ = v_snd_1320_;
v_isShared_1337_ = v_isSharedCheck_1594_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snd_1334_);
lean_inc(v_fst_1333_);
lean_dec(v_snd_1320_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1594_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_ref_1338_; lean_object* v_quotContext_1339_; lean_object* v_currMacroScope_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_ref_1338_ = lean_ctor_get(v___y_1310_, 5);
v_quotContext_1339_ = lean_ctor_get(v___y_1310_, 10);
v_currMacroScope_1340_ = lean_ctor_get(v___y_1310_, 11);
v___x_1341_ = l_Lean_SourceInfo_fromRef(v_ref_1338_, v___x_1303_);
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_1343_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5));
v___x_1344_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
v___x_1345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
lean_inc(v___x_1341_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 2, v___x_1345_);
lean_ctor_set(v___x_1299_, 1, v___x_1342_);
lean_ctor_set(v___x_1299_, 0, v___x_1341_);
v___x_1347_ = v___x_1299_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_inc_ref_n(v___x_1347_, 7);
lean_inc_n(v___x_1341_, 2);
v___x_1348_ = l_Lean_Syntax_node7(v___x_1341_, v___x_1344_, v___x_1347_, v___x_1347_, v___x_1347_, v___x_1347_, v___x_1347_, v___x_1347_, v___x_1347_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8));
v___x_1350_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9));
v___x_1351_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11));
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 2);
lean_ctor_set(v___x_1336_, 1, v___x_1349_);
lean_ctor_set(v___x_1336_, 0, v___x_1341_);
v___x_1353_ = v___x_1336_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1349_);
v___x_1353_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_inc_n(v___x_1341_, 5);
v___x_1354_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1351_, v___x_1353_);
v___x_1355_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13));
v___x_1356_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15);
v___x_1357_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
lean_inc(v_currMacroScope_1340_);
lean_inc(v_quotContext_1339_);
v___x_1358_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1357_, v_currMacroScope_1340_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1341_);
lean_ctor_set(v___x_1360_, 1, v___x_1356_);
lean_ctor_set(v___x_1360_, 2, v___x_1358_);
lean_ctor_set(v___x_1360_, 3, v___x_1359_);
lean_inc_ref_n(v___x_1347_, 3);
lean_inc_ref(v___x_1360_);
v___x_1361_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1355_, v___x_1360_, v___x_1347_);
v___x_1362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_1363_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1362_, v___x_1347_, v___x_1347_);
v___x_1364_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17));
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 2);
lean_ctor_set(v___x_1331_, 1, v___x_1364_);
lean_ctor_set(v___x_1331_, 0, v___x_1341_);
v___x_1366_ = v___x_1331_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; size_t v_sz_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19));
v___x_1368_ = l_Array_zip___redArg(v_fst_1325_, v_fst_1329_);
lean_dec(v_fst_1329_);
lean_dec(v_fst_1325_);
v_sz_1369_ = lean_array_size(v___x_1368_);
lean_inc(v___x_1348_);
lean_inc_ref_n(v___x_1347_, 2);
lean_inc_n(v___x_1341_, 5);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(v___x_1341_, v___x_1347_, v___x_1348_, v_sz_1369_, v___x_1314_, v___x_1368_);
v___x_1371_ = l_Array_append___redArg(v___x_1345_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1341_);
lean_ctor_set(v___x_1372_, 1, v___x_1342_);
lean_ctor_set(v___x_1372_, 2, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1367_, v___x_1372_);
lean_inc_ref(v___x_1366_);
v___x_1374_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1342_, v___x_1366_, v___x_1347_, v___x_1373_);
v___x_1375_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21));
v___x_1376_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22));
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 2);
lean_ctor_set(v___x_1327_, 1, v___x_1376_);
lean_ctor_set(v___x_1327_, 0, v___x_1341_);
v___x_1378_ = v___x_1327_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; size_t v_sz_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; size_t v_sz_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24));
v___x_1380_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26);
v___x_1381_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27));
lean_inc_n(v_currMacroScope_1340_, 12);
lean_inc_n(v_quotContext_1339_, 12);
v___x_1382_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1381_, v_currMacroScope_1340_);
v___x_1383_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32));
lean_inc_n(v___x_1341_, 102);
v___x_1384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1341_);
lean_ctor_set(v___x_1384_, 1, v___x_1380_);
lean_ctor_set(v___x_1384_, 2, v___x_1382_);
lean_ctor_set(v___x_1384_, 3, v___x_1383_);
lean_inc_ref_n(v___x_1347_, 34);
v___x_1385_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1379_, v___x_1347_, v___x_1384_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33));
v___x_1387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1341_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35);
v___x_1389_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36));
v___x_1390_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1389_, v_currMacroScope_1340_);
v___x_1391_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41));
v___x_1392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1341_);
lean_ctor_set(v___x_1392_, 1, v___x_1388_);
lean_ctor_set(v___x_1392_, 2, v___x_1390_);
lean_ctor_set(v___x_1392_, 3, v___x_1391_);
v___x_1393_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1379_, v___x_1347_, v___x_1392_);
lean_inc_ref(v___x_1387_);
v___x_1394_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1342_, v___x_1385_, v___x_1387_, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1342_, v___x_1378_, v___x_1394_);
v___x_1396_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1375_, v___x_1395_);
v___x_1397_ = l_Lean_Syntax_node6(v___x_1341_, v___x_1350_, v___x_1354_, v___x_1361_, v___x_1363_, v___x_1347_, v___x_1374_, v___x_1396_);
lean_inc(v___x_1348_);
v___x_1398_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1343_, v___x_1348_, v___x_1397_);
v___x_1399_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42));
v___x_1400_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43));
v___x_1401_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44));
v___x_1402_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45));
v___x_1403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1341_);
lean_ctor_set(v___x_1403_, 1, v___x_1401_);
v___x_1404_ = l_Array_append___redArg(v___x_1345_, v_encInstBinders_1285_);
v___x_1405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1341_);
lean_ctor_set(v___x_1405_, 1, v___x_1342_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
v___x_1406_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1402_, v___x_1403_, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1341_);
lean_ctor_set(v___x_1407_, 1, v___x_1399_);
v___x_1408_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46));
v___x_1409_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47));
v___x_1410_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49));
v___x_1411_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1410_, v___x_1347_);
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1341_);
lean_ctor_set(v___x_1412_, 1, v___x_1408_);
v___x_1413_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51));
v___x_1414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_1415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_1416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1341_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_1418_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52);
v___x_1419_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
v___x_1420_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1419_, v_currMacroScope_1340_);
v___x_1421_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56));
v___x_1422_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1341_);
lean_ctor_set(v___x_1422_, 1, v___x_1418_);
lean_ctor_set(v___x_1422_, 2, v___x_1420_);
lean_ctor_set(v___x_1422_, 3, v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
v___x_1424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
v___x_1425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
v___x_1426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1341_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
v___x_1428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56);
v___x_1429_ = lean_box(0);
v___x_1430_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1429_, v_currMacroScope_1340_);
v___x_1431_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62));
v___x_1432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1341_);
lean_ctor_set(v___x_1432_, 1, v___x_1428_);
lean_ctor_set(v___x_1432_, 2, v___x_1430_);
lean_ctor_set(v___x_1432_, 3, v___x_1431_);
v___x_1433_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1427_, v___x_1432_);
v___x_1434_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1424_, v___x_1426_, v___x_1433_);
v___x_1435_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64));
v___x_1436_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65));
v___x_1437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1341_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Lean_mkCIdent(v_name_1297_);
v___x_1439_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1435_, v___x_1437_, v___x_1438_);
v_sz_1440_ = lean_array_size(v_a_1321_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(v_sz_1440_, v___x_1314_, v_a_1321_);
v___x_1442_ = l_Array_append___redArg(v___x_1345_, v___x_1441_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1341_);
lean_ctor_set(v___x_1443_, 1, v___x_1342_);
lean_ctor_set(v___x_1443_, 2, v___x_1442_);
v___x_1444_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1417_, v___x_1439_, v___x_1443_);
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_1446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1341_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1423_, v___x_1434_, v___x_1444_, v___x_1446_);
v___x_1448_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1447_);
v___x_1449_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1417_, v___x_1422_, v___x_1448_);
lean_inc_ref_n(v___x_1416_, 2);
v___x_1450_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1414_, v___x_1416_, v___x_1449_);
v___x_1451_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1413_, v___x_1347_, v___x_1450_);
v___x_1452_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67));
v___x_1453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_1454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1341_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69));
v___x_1456_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70));
v___x_1457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1341_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72));
v___x_1459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_1460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_1461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21);
v___x_1462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
v___x_1463_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1462_, v_currMacroScope_1340_);
v___x_1464_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74));
v___x_1465_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1341_);
lean_ctor_set(v___x_1465_, 1, v___x_1461_);
lean_ctor_set(v___x_1465_, 2, v___x_1463_);
lean_ctor_set(v___x_1465_, 3, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1460_, v___x_1465_, v___x_1347_);
v___x_1467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_1468_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76);
v___x_1469_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77));
v___x_1470_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1469_, v_currMacroScope_1340_);
v___x_1471_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1341_);
lean_ctor_set(v___x_1471_, 1, v___x_1468_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
lean_ctor_set(v___x_1471_, 3, v___x_1359_);
lean_inc_ref(v___x_1471_);
lean_inc_ref_n(v___x_1454_, 4);
v___x_1472_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1467_, v___x_1454_, v___x_1347_, v___x_1471_);
v___x_1473_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1342_, v___x_1347_, v___x_1347_, v___x_1472_);
v___x_1474_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1459_, v___x_1466_, v___x_1473_);
v___x_1475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37);
v___x_1476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
v___x_1477_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1476_, v_currMacroScope_1340_);
v___x_1478_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79));
v___x_1479_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1341_);
lean_ctor_set(v___x_1479_, 1, v___x_1475_);
lean_ctor_set(v___x_1479_, 2, v___x_1477_);
lean_ctor_set(v___x_1479_, 3, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1460_, v___x_1479_, v___x_1347_);
v___x_1481_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81);
v___x_1482_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82));
v___x_1483_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1482_, v_currMacroScope_1340_);
v___x_1484_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1341_);
lean_ctor_set(v___x_1484_, 1, v___x_1481_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
lean_ctor_set(v___x_1484_, 3, v___x_1359_);
lean_inc_ref(v___x_1484_);
v___x_1485_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1467_, v___x_1454_, v___x_1347_, v___x_1484_);
v___x_1486_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1342_, v___x_1347_, v___x_1347_, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1459_, v___x_1480_, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1342_, v___x_1474_, v___x_1387_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1458_, v___x_1488_);
v___x_1490_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84));
v___x_1491_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1490_, v___x_1347_);
v___x_1492_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85));
v___x_1493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1341_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
lean_inc_ref_n(v___x_1493_, 2);
lean_inc_n(v___x_1491_, 2);
lean_inc_ref_n(v___x_1457_, 2);
v___x_1494_ = l_Lean_Syntax_node6(v___x_1341_, v___x_1455_, v___x_1457_, v___x_1347_, v___x_1489_, v___x_1491_, v___x_1347_, v___x_1493_);
v___x_1495_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88));
v___x_1496_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1495_, v___x_1347_, v___x_1347_);
v___x_1497_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90));
v___x_1498_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92));
v___x_1499_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94));
v___x_1500_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96));
v___x_1501_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98));
v___x_1502_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1501_, v___x_1471_);
v___x_1503_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30);
v___x_1504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
v___x_1505_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1504_, v_currMacroScope_1340_);
v___x_1506_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1341_);
lean_ctor_set(v___x_1506_, 1, v___x_1503_);
lean_ctor_set(v___x_1506_, 2, v___x_1505_);
lean_ctor_set(v___x_1506_, 3, v___x_1359_);
lean_inc_ref(v___x_1506_);
v___x_1507_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1506_);
v___x_1508_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100));
v___x_1509_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101));
v___x_1510_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1341_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103);
v___x_1512_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104));
v___x_1513_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1512_, v_currMacroScope_1340_);
v___x_1514_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107));
v___x_1515_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1341_);
lean_ctor_set(v___x_1515_, 1, v___x_1511_);
lean_ctor_set(v___x_1515_, 2, v___x_1513_);
lean_ctor_set(v___x_1515_, 3, v___x_1514_);
v_sz_1516_ = lean_array_size(v_fst_1333_);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_1516_, v___x_1314_, v_fst_1333_);
v___x_1518_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108);
v___x_1519_ = l_Lean_mkSepArray(v___x_1517_, v___x_1518_);
lean_dec_ref(v___x_1517_);
v___x_1520_ = l_Array_append___redArg(v___x_1345_, v___x_1519_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1341_);
lean_ctor_set(v___x_1521_, 1, v___x_1342_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
v___x_1522_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1458_, v___x_1521_);
lean_inc_ref(v___x_1360_);
v___x_1523_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1342_, v___x_1416_, v___x_1360_);
v___x_1524_ = l_Lean_Syntax_node6(v___x_1341_, v___x_1455_, v___x_1457_, v___x_1347_, v___x_1522_, v___x_1491_, v___x_1523_, v___x_1493_);
v___x_1525_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1524_);
v___x_1526_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1417_, v___x_1515_, v___x_1525_);
v___x_1527_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1526_);
lean_inc_ref(v___x_1510_);
v___x_1528_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1508_, v___x_1510_, v___x_1527_);
v___x_1529_ = l_Lean_Syntax_node5(v___x_1341_, v___x_1500_, v___x_1502_, v___x_1507_, v___x_1347_, v___x_1454_, v___x_1528_);
v___x_1530_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1499_, v___x_1529_);
lean_inc_n(v___x_1496_, 2);
v___x_1531_ = l_Lean_Syntax_node4(v___x_1341_, v___x_1498_, v___x_1347_, v___x_1347_, v___x_1530_, v___x_1496_);
v___x_1532_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1501_, v___x_1484_);
v___x_1533_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110);
v___x_1534_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111));
v___x_1535_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1534_, v_currMacroScope_1340_);
v___x_1536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1341_);
lean_ctor_set(v___x_1536_, 1, v___x_1533_);
lean_ctor_set(v___x_1536_, 2, v___x_1535_);
lean_ctor_set(v___x_1536_, 3, v___x_1359_);
v___x_1537_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1536_);
v___x_1538_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112));
v___x_1539_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113));
v___x_1540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1341_);
lean_ctor_set(v___x_1540_, 1, v___x_1538_);
v___x_1541_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115));
v___x_1542_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117));
v___x_1543_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119));
v___x_1544_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120));
v___x_1545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1341_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122));
v___x_1547_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1546_, v___x_1347_);
v___x_1548_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124));
v___x_1549_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1414_, v___x_1416_, v___x_1360_);
v___x_1550_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1549_);
v___x_1551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_1552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1341_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126));
v___x_1554_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128);
v___x_1555_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129));
v___x_1556_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1555_, v_currMacroScope_1340_);
v___x_1557_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132));
v___x_1558_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1341_);
lean_ctor_set(v___x_1558_, 1, v___x_1554_);
lean_ctor_set(v___x_1558_, 2, v___x_1556_);
lean_ctor_set(v___x_1558_, 3, v___x_1557_);
lean_inc(v___x_1537_);
v___x_1559_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1417_, v___x_1558_, v___x_1537_);
v___x_1560_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1553_, v___x_1559_);
v___x_1561_ = l_Lean_Syntax_node4(v___x_1341_, v___x_1548_, v___x_1506_, v___x_1550_, v___x_1552_, v___x_1560_);
v___x_1562_ = l_Lean_Syntax_node4(v___x_1341_, v___x_1543_, v___x_1545_, v___x_1347_, v___x_1547_, v___x_1561_);
v___x_1563_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1542_, v___x_1562_, v___x_1347_);
v___x_1564_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134));
v___x_1565_ = l_Lean_Syntax_SepArray_ofElems(v___x_1386_, v_snd_1334_);
lean_dec(v_snd_1334_);
v___x_1566_ = l_Array_append___redArg(v___x_1345_, v___x_1565_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1341_);
lean_ctor_set(v___x_1567_, 1, v___x_1342_);
lean_ctor_set(v___x_1567_, 2, v___x_1566_);
v___x_1568_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1458_, v___x_1567_);
v___x_1569_ = l_Lean_Syntax_node6(v___x_1341_, v___x_1455_, v___x_1457_, v___x_1347_, v___x_1568_, v___x_1491_, v___x_1347_, v___x_1493_);
v___x_1570_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1569_);
v___x_1571_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1564_, v___x_1510_, v___x_1570_);
v___x_1572_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1542_, v___x_1571_, v___x_1347_);
v___x_1573_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1342_, v___x_1563_, v___x_1572_);
v___x_1574_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1541_, v___x_1573_);
v___x_1575_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1539_, v___x_1540_, v___x_1574_);
v___x_1576_ = l_Lean_Syntax_node5(v___x_1341_, v___x_1500_, v___x_1532_, v___x_1537_, v___x_1347_, v___x_1454_, v___x_1575_);
v___x_1577_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1499_, v___x_1576_);
v___x_1578_ = l_Lean_Syntax_node4(v___x_1341_, v___x_1498_, v___x_1347_, v___x_1347_, v___x_1577_, v___x_1496_);
v___x_1579_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1342_, v___x_1531_, v___x_1347_, v___x_1578_);
v___x_1580_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1497_, v___x_1366_, v___x_1579_, v___x_1347_);
v___x_1581_ = l_Lean_Syntax_node1(v___x_1341_, v___x_1342_, v___x_1580_);
v___x_1582_ = l_Lean_Syntax_node4(v___x_1341_, v___x_1452_, v___x_1454_, v___x_1494_, v___x_1496_, v___x_1581_);
v___x_1583_ = l_Lean_Syntax_node6(v___x_1341_, v___x_1409_, v___x_1411_, v___x_1412_, v___x_1347_, v___x_1347_, v___x_1451_, v___x_1582_);
v___x_1584_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1343_, v___x_1348_, v___x_1583_);
v___x_1585_ = l_Lean_Syntax_node3(v___x_1341_, v___x_1400_, v___x_1406_, v___x_1407_, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_node2(v___x_1341_, v___x_1342_, v___x_1398_, v___x_1585_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1586_);
v___x_1588_ = v___x_1323_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1316_);
lean_del_object(v___x_1299_);
lean_dec(v_name_1297_);
v_a_1600_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1318_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1318_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_del_object(v___x_1299_);
lean_dec(v_name_1297_);
lean_dec_ref(v_params_1284_);
v_a_1608_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1315_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1315_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___boxed(lean_object* v_indVal_1641_, lean_object* v_params_1642_, lean_object* v_encInstBinders_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(v_indVal_1641_, v_params_1642_, v_encInstBinders_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec_ref(v_encInstBinders_1643_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(lean_object* v_00_u03b1_1652_, lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v_msg_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_msg_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(v_00_u03b1_1662_, v_msg_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_bs_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_1672_, v_i_1673_, v_bs_1674_, v___y_1677_, v___y_1679_, v___y_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___boxed(lean_object* v_sz_1683_, lean_object* v_i_1684_, lean_object* v_bs_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
size_t v_sz_boxed_1693_; size_t v_i_boxed_1694_; lean_object* v_res_1695_; 
v_sz_boxed_1693_ = lean_unbox_usize(v_sz_1683_);
lean_dec(v_sz_1683_);
v_i_boxed_1694_ = lean_unbox_usize(v_i_1684_);
lean_dec(v_i_1684_);
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(v_sz_boxed_1693_, v_i_boxed_1694_, v_bs_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(lean_object* v_cls_1696_, lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v_cls_1696_, v_msg_1697_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___boxed(lean_object* v_cls_1706_, lean_object* v_msg_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(v_cls_1706_, v_msg_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1(lean_object* v_msgData_1716_, lean_object* v_macroStack_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg(v_msgData_1716_, v_macroStack_1717_, v___y_1722_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___boxed(lean_object* v_msgData_1726_, lean_object* v_macroStack_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1(v_msgData_1726_, v_macroStack_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1735_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = l_Lean_Parser_termParser(v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0);
v___x_1739_ = l_Lean_Parser_Term_matchAlt(v___x_1738_);
return v___x_1739_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm(void){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(lean_object* v_s_1741_){
_start:
{
lean_inc(v_s_1741_);
return v_s_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed(lean_object* v_s_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(v_s_1742_);
lean_dec(v_s_1742_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(lean_object* v___x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_quotContext_1750_; lean_object* v_currMacroScope_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_quotContext_1750_ = lean_ctor_get(v___y_1747_, 10);
lean_inc(v_quotContext_1750_);
v_currMacroScope_1751_ = lean_ctor_get(v___y_1747_, 11);
lean_inc(v_currMacroScope_1751_);
lean_dec_ref(v___y_1747_);
v___x_1752_ = l_Lean_addMacroScope(v_quotContext_1750_, v___x_1746_, v_currMacroScope_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed(lean_object* v___x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(v___x_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___f_1767_; lean_object* v___x_1768_; 
v___f_1767_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2));
v___x_1768_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_1767_, v___y_1764_, v___y_1765_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___boxed(lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(v___y_1777_, v___y_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___boxed(lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0(lean_object* v_k_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v_b_1792_, lean_object* v_c_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
lean_inc(v___y_1797_);
lean_inc_ref(v___y_1796_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
v___x_1799_ = lean_apply_9(v_k_1789_, v_b_1792_, v_c_1793_, v___y_1790_, v___y_1791_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, lean_box(0));
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0___boxed(lean_object* v_k_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v_b_1803_, lean_object* v_c_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0(v_k_1800_, v___y_1801_, v___y_1802_, v_b_1803_, v_c_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(lean_object* v_type_1811_, lean_object* v_k_1812_, uint8_t v_cleanupAnnotations_1813_, uint8_t v_whnfType_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___f_1822_; lean_object* v___x_1823_; 
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1822_, 0, v_k_1812_);
lean_closure_set(v___f_1822_, 1, v___y_1815_);
lean_closure_set(v___f_1822_, 2, v___y_1816_);
v___x_1823_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1811_, v___f_1822_, v_cleanupAnnotations_1813_, v_whnfType_1814_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1823_) == 0)
{
return v___x_1823_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___boxed(lean_object* v_type_1832_, lean_object* v_k_1833_, lean_object* v_cleanupAnnotations_1834_, lean_object* v_whnfType_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1843_; uint8_t v_whnfType_boxed_1844_; lean_object* v_res_1845_; 
v_cleanupAnnotations_boxed_1843_ = lean_unbox(v_cleanupAnnotations_1834_);
v_whnfType_boxed_1844_ = lean_unbox(v_whnfType_1835_);
v_res_1845_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(v_type_1832_, v_k_1833_, v_cleanupAnnotations_boxed_1843_, v_whnfType_boxed_1844_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(lean_object* v_00_u03b1_1846_, lean_object* v_type_1847_, lean_object* v_k_1848_, uint8_t v_cleanupAnnotations_1849_, uint8_t v_whnfType_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(v_type_1847_, v_k_1848_, v_cleanupAnnotations_1849_, v_whnfType_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_type_1860_, lean_object* v_k_1861_, lean_object* v_cleanupAnnotations_1862_, lean_object* v_whnfType_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1871_; uint8_t v_whnfType_boxed_1872_; lean_object* v_res_1873_; 
v_cleanupAnnotations_boxed_1871_ = lean_unbox(v_cleanupAnnotations_1862_);
v_whnfType_boxed_1872_ = lean_unbox(v_whnfType_1863_);
v_res_1873_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(v_00_u03b1_1859_, v_type_1860_, v_k_1861_, v_cleanupAnnotations_boxed_1871_, v_whnfType_boxed_1872_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(size_t v_sz_1874_, size_t v_i_1875_, lean_object* v_bs_1876_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_usize_dec_lt(v_i_1875_, v_sz_1874_);
if (v___x_1877_ == 0)
{
return v_bs_1876_;
}
else
{
lean_object* v_v_1878_; lean_object* v___x_1879_; lean_object* v_bs_x27_1880_; size_t v___x_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v_v_1878_ = lean_array_uget(v_bs_1876_, v_i_1875_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v_bs_x27_1880_ = lean_array_uset(v_bs_1876_, v_i_1875_, v___x_1879_);
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_add(v_i_1875_, v___x_1881_);
v___x_1883_ = lean_array_uset(v_bs_x27_1880_, v_i_1875_, v_v_1878_);
v_i_1875_ = v___x_1882_;
v_bs_1876_ = v___x_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15___boxed(lean_object* v_sz_1885_, lean_object* v_i_1886_, lean_object* v_bs_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1885_);
lean_dec(v_sz_1885_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(v_sz_boxed_1888_, v_i_boxed_1889_, v_bs_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(size_t v_sz_1891_, size_t v_i_1892_, lean_object* v_bs_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_lt(v_i_1892_, v_sz_1891_);
if (v___x_1894_ == 0)
{
return v_bs_1893_;
}
else
{
lean_object* v_v_1895_; lean_object* v___x_1896_; lean_object* v_bs_x27_1897_; size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_v_1895_ = lean_array_uget(v_bs_1893_, v_i_1892_);
v___x_1896_ = lean_unsigned_to_nat(0u);
v_bs_x27_1897_ = lean_array_uset(v_bs_1893_, v_i_1892_, v___x_1896_);
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_add(v_i_1892_, v___x_1898_);
v___x_1900_ = lean_array_uset(v_bs_x27_1897_, v_i_1892_, v_v_1895_);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(v_sz_1891_, v___x_1899_, v___x_1900_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___boxed(lean_object* v_sz_1902_, lean_object* v_i_1903_, lean_object* v_bs_1904_){
_start:
{
size_t v_sz_boxed_1905_; size_t v_i_boxed_1906_; lean_object* v_res_1907_; 
v_sz_boxed_1905_ = lean_unbox_usize(v_sz_1902_);
lean_dec(v_sz_1902_);
v_i_boxed_1906_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(v_sz_boxed_1905_, v_i_boxed_1906_, v_bs_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(size_t v_sz_1908_, size_t v_i_1909_, lean_object* v_bs_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_usize_dec_lt(v_i_1909_, v_sz_1908_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_bs_1910_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v_bs_x27_1923_; lean_object* v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = lean_unsigned_to_nat(0u);
v_bs_x27_1923_ = lean_array_uset(v_bs_1910_, v_i_1909_, v___x_1922_);
v___x_1924_ = lean_mk_syntax_ident(v_a_1921_);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1909_, v___x_1925_);
v___x_1927_ = lean_array_uset(v_bs_x27_1923_, v_i_1909_, v___x_1924_);
v_i_1909_ = v___x_1926_;
v_bs_1910_ = v___x_1927_;
goto _start;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_bs_1910_);
v_a_1929_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1920_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1920_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5___boxed(lean_object* v_sz_1937_, lean_object* v_i_1938_, lean_object* v_bs_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
size_t v_sz_boxed_1947_; size_t v_i_boxed_1948_; lean_object* v_res_1949_; 
v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1937_);
lean_dec(v_sz_1937_);
v_i_boxed_1948_ = lean_unbox_usize(v_i_1938_);
lean_dec(v_i_1938_);
v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(v_sz_boxed_1947_, v_i_boxed_1948_, v_bs_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(size_t v_sz_1950_, size_t v_i_1951_, lean_object* v_bs_1952_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_usize_dec_lt(v_i_1951_, v_sz_1950_);
if (v___x_1953_ == 0)
{
return v_bs_1952_;
}
else
{
lean_object* v_v_1954_; lean_object* v___x_1955_; lean_object* v_bs_x27_1956_; size_t v___x_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v_v_1954_ = lean_array_uget(v_bs_1952_, v_i_1951_);
v___x_1955_ = lean_unsigned_to_nat(0u);
v_bs_x27_1956_ = lean_array_uset(v_bs_1952_, v_i_1951_, v___x_1955_);
v___x_1957_ = ((size_t)1ULL);
v___x_1958_ = lean_usize_add(v_i_1951_, v___x_1957_);
v___x_1959_ = lean_array_uset(v_bs_x27_1956_, v_i_1951_, v_v_1954_);
v_i_1951_ = v___x_1958_;
v_bs_1952_ = v___x_1959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3___boxed(lean_object* v_sz_1961_, lean_object* v_i_1962_, lean_object* v_bs_1963_){
_start:
{
size_t v_sz_boxed_1964_; size_t v_i_boxed_1965_; lean_object* v_res_1966_; 
v_sz_boxed_1964_ = lean_unbox_usize(v_sz_1961_);
lean_dec(v_sz_1961_);
v_i_boxed_1965_ = lean_unbox_usize(v_i_1962_);
lean_dec(v_i_1962_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(v_sz_boxed_1964_, v_i_boxed_1965_, v_bs_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(size_t v_sz_1967_, size_t v_i_1968_, lean_object* v_bs_1969_, lean_object* v___y_1970_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_usize_dec_lt(v_i_1968_, v_sz_1967_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_bs_1969_);
return v___x_1973_;
}
else
{
lean_object* v_ref_1974_; lean_object* v_quotContext_1975_; lean_object* v_currMacroScope_1976_; lean_object* v_v_1977_; lean_object* v___x_1978_; lean_object* v_bs_x27_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v_ref_1974_ = lean_ctor_get(v___y_1970_, 5);
v_quotContext_1975_ = lean_ctor_get(v___y_1970_, 10);
v_currMacroScope_1976_ = lean_ctor_get(v___y_1970_, 11);
v_v_1977_ = lean_array_uget(v_bs_1969_, v_i_1968_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v_bs_x27_1979_ = lean_array_uset(v_bs_1969_, v_i_1968_, v___x_1978_);
v___x_1980_ = 0;
v___x_1981_ = l_Lean_SourceInfo_fromRef(v_ref_1974_, v___x_1980_);
v___x_1982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_1983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_1981_, 4);
v___x_1984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1981_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_1986_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37);
v___x_1987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
lean_inc(v_currMacroScope_1976_);
lean_inc(v_quotContext_1975_);
v___x_1988_ = l_Lean_addMacroScope(v_quotContext_1975_, v___x_1987_, v_currMacroScope_1976_);
v___x_1989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41));
v___x_1990_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1981_);
lean_ctor_set(v___x_1990_, 1, v___x_1986_);
lean_ctor_set(v___x_1990_, 2, v___x_1988_);
lean_ctor_set(v___x_1990_, 3, v___x_1989_);
v___x_1991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_1992_ = l_Lean_Syntax_node1(v___x_1981_, v___x_1991_, v_v_1977_);
v___x_1993_ = l_Lean_Syntax_node2(v___x_1981_, v___x_1985_, v___x_1990_, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_node2(v___x_1981_, v___x_1982_, v___x_1984_, v___x_1993_);
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_add(v_i_1968_, v___x_1995_);
v___x_1997_ = lean_array_uset(v_bs_x27_1979_, v_i_1968_, v___x_1994_);
v_i_1968_ = v___x_1996_;
v_bs_1969_ = v___x_1997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg___boxed(lean_object* v_sz_1999_, lean_object* v_i_2000_, lean_object* v_bs_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
size_t v_sz_boxed_2004_; size_t v_i_boxed_2005_; lean_object* v_res_2006_; 
v_sz_boxed_2004_ = lean_unbox_usize(v_sz_1999_);
lean_dec(v_sz_1999_);
v_i_boxed_2005_ = lean_unbox_usize(v_i_2000_);
lean_dec(v_i_2000_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(v_sz_boxed_2004_, v_i_boxed_2005_, v_bs_2001_, v___y_2002_);
lean_dec_ref(v___y_2002_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(size_t v_sz_2007_, size_t v_i_2008_, lean_object* v_bs_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2008_, v_sz_2007_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_bs_2009_);
return v___x_2018_;
}
else
{
lean_object* v_ref_2019_; lean_object* v_quotContext_2020_; lean_object* v_currMacroScope_2021_; lean_object* v_v_2022_; lean_object* v___x_2023_; lean_object* v_bs_x27_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_ref_2019_ = lean_ctor_get(v___y_2014_, 5);
v_quotContext_2020_ = lean_ctor_get(v___y_2014_, 10);
v_currMacroScope_2021_ = lean_ctor_get(v___y_2014_, 11);
v_v_2022_ = lean_array_uget(v_bs_2009_, v_i_2008_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v_bs_x27_2024_ = lean_array_uset(v_bs_2009_, v_i_2008_, v___x_2023_);
v___x_2025_ = 0;
v___x_2026_ = l_Lean_SourceInfo_fromRef(v_ref_2019_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2026_, 4);
v___x_2029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2026_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37);
v___x_2032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
lean_inc(v_currMacroScope_2021_);
lean_inc(v_quotContext_2020_);
v___x_2033_ = l_Lean_addMacroScope(v_quotContext_2020_, v___x_2032_, v_currMacroScope_2021_);
v___x_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41));
v___x_2035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2026_);
lean_ctor_set(v___x_2035_, 1, v___x_2031_);
lean_ctor_set(v___x_2035_, 2, v___x_2033_);
lean_ctor_set(v___x_2035_, 3, v___x_2034_);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2037_ = l_Lean_Syntax_node1(v___x_2026_, v___x_2036_, v_v_2022_);
v___x_2038_ = l_Lean_Syntax_node2(v___x_2026_, v___x_2030_, v___x_2035_, v___x_2037_);
v___x_2039_ = l_Lean_Syntax_node2(v___x_2026_, v___x_2027_, v___x_2029_, v___x_2038_);
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_add(v_i_2008_, v___x_2040_);
v___x_2042_ = lean_array_uset(v_bs_x27_2024_, v_i_2008_, v___x_2039_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(v_sz_2007_, v___x_2041_, v___x_2042_, v___y_2014_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8___boxed(lean_object* v_sz_2044_, lean_object* v_i_2045_, lean_object* v_bs_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
size_t v_sz_boxed_2054_; size_t v_i_boxed_2055_; lean_object* v_res_2056_; 
v_sz_boxed_2054_ = lean_unbox_usize(v_sz_2044_);
lean_dec(v_sz_2044_);
v_i_boxed_2055_ = lean_unbox_usize(v_i_2045_);
lean_dec(v_i_2045_);
v_res_2056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(v_sz_boxed_2054_, v_i_boxed_2055_, v_bs_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_bs_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_bs_2059_);
return v___x_2063_;
}
else
{
lean_object* v_ref_2064_; lean_object* v_quotContext_2065_; lean_object* v_currMacroScope_2066_; lean_object* v_v_2067_; lean_object* v___x_2068_; lean_object* v_bs_x27_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; 
v_ref_2064_ = lean_ctor_get(v___y_2060_, 5);
v_quotContext_2065_ = lean_ctor_get(v___y_2060_, 10);
v_currMacroScope_2066_ = lean_ctor_get(v___y_2060_, 11);
v_v_2067_ = lean_array_uget(v_bs_2059_, v_i_2058_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v_bs_x27_2069_ = lean_array_uset(v_bs_2059_, v_i_2058_, v___x_2068_);
v___x_2070_ = 0;
v___x_2071_ = l_Lean_SourceInfo_fromRef(v_ref_2064_, v___x_2070_);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2071_, 4);
v___x_2074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2071_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21);
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
lean_inc(v_currMacroScope_2066_);
lean_inc(v_quotContext_2065_);
v___x_2078_ = l_Lean_addMacroScope(v_quotContext_2065_, v___x_2077_, v_currMacroScope_2066_);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26));
v___x_2080_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2071_);
lean_ctor_set(v___x_2080_, 1, v___x_2076_);
lean_ctor_set(v___x_2080_, 2, v___x_2078_);
lean_ctor_set(v___x_2080_, 3, v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2082_ = l_Lean_Syntax_node1(v___x_2071_, v___x_2081_, v_v_2067_);
v___x_2083_ = l_Lean_Syntax_node2(v___x_2071_, v___x_2075_, v___x_2080_, v___x_2082_);
v___x_2084_ = l_Lean_Syntax_node2(v___x_2071_, v___x_2072_, v___x_2074_, v___x_2083_);
v___x_2085_ = ((size_t)1ULL);
v___x_2086_ = lean_usize_add(v_i_2058_, v___x_2085_);
v___x_2087_ = lean_array_uset(v_bs_x27_2069_, v_i_2058_, v___x_2084_);
v_i_2058_ = v___x_2086_;
v_bs_2059_ = v___x_2087_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg___boxed(lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_bs_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2091_, v___y_2092_);
lean_dec_ref(v___y_2092_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(size_t v_sz_2097_, size_t v_i_2098_, lean_object* v_bs_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_usize_dec_lt(v_i_2098_, v_sz_2097_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_bs_2099_);
return v___x_2108_;
}
else
{
lean_object* v_ref_2109_; lean_object* v_quotContext_2110_; lean_object* v_currMacroScope_2111_; lean_object* v_v_2112_; lean_object* v___x_2113_; lean_object* v_bs_x27_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_ref_2109_ = lean_ctor_get(v___y_2104_, 5);
v_quotContext_2110_ = lean_ctor_get(v___y_2104_, 10);
v_currMacroScope_2111_ = lean_ctor_get(v___y_2104_, 11);
v_v_2112_ = lean_array_uget(v_bs_2099_, v_i_2098_);
v___x_2113_ = lean_unsigned_to_nat(0u);
v_bs_x27_2114_ = lean_array_uset(v_bs_2099_, v_i_2098_, v___x_2113_);
v___x_2115_ = 0;
v___x_2116_ = l_Lean_SourceInfo_fromRef(v_ref_2109_, v___x_2115_);
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2116_, 4);
v___x_2119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21);
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
lean_inc(v_currMacroScope_2111_);
lean_inc(v_quotContext_2110_);
v___x_2123_ = l_Lean_addMacroScope(v_quotContext_2110_, v___x_2122_, v_currMacroScope_2111_);
v___x_2124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26));
v___x_2125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2116_);
lean_ctor_set(v___x_2125_, 1, v___x_2121_);
lean_ctor_set(v___x_2125_, 2, v___x_2123_);
lean_ctor_set(v___x_2125_, 3, v___x_2124_);
v___x_2126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2127_ = l_Lean_Syntax_node1(v___x_2116_, v___x_2126_, v_v_2112_);
v___x_2128_ = l_Lean_Syntax_node2(v___x_2116_, v___x_2120_, v___x_2125_, v___x_2127_);
v___x_2129_ = l_Lean_Syntax_node2(v___x_2116_, v___x_2117_, v___x_2119_, v___x_2128_);
v___x_2130_ = ((size_t)1ULL);
v___x_2131_ = lean_usize_add(v_i_2098_, v___x_2130_);
v___x_2132_ = lean_array_uset(v_bs_x27_2114_, v_i_2098_, v___x_2129_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(v_sz_2097_, v___x_2131_, v___x_2132_, v___y_2104_);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7___boxed(lean_object* v_sz_2134_, lean_object* v_i_2135_, lean_object* v_bs_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2134_);
lean_dec(v_sz_2134_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(v_sz_boxed_2144_, v_i_boxed_2145_, v_bs_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_bs_2149_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2150_ == 0)
{
return v_bs_2149_;
}
else
{
lean_object* v_v_2151_; lean_object* v___x_2152_; lean_object* v_bs_x27_2153_; size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v_v_2151_ = lean_array_uget(v_bs_2149_, v_i_2148_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v_bs_x27_2153_ = lean_array_uset(v_bs_2149_, v_i_2148_, v___x_2152_);
v___x_2154_ = ((size_t)1ULL);
v___x_2155_ = lean_usize_add(v_i_2148_, v___x_2154_);
v___x_2156_ = lean_array_uset(v_bs_x27_2153_, v_i_2148_, v_v_2151_);
v_i_2148_ = v___x_2155_;
v_bs_2149_ = v___x_2156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2___boxed(lean_object* v_sz_2158_, lean_object* v_i_2159_, lean_object* v_bs_2160_){
_start:
{
size_t v_sz_boxed_2161_; size_t v_i_boxed_2162_; lean_object* v_res_2163_; 
v_sz_boxed_2161_ = lean_unbox_usize(v_sz_2158_);
lean_dec(v_sz_2158_);
v_i_boxed_2162_ = lean_unbox_usize(v_i_2159_);
lean_dec(v_i_2159_);
v_res_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(v_sz_boxed_2161_, v_i_boxed_2162_, v_bs_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_bs_2166_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_lt(v_i_2165_, v_sz_2164_);
if (v___x_2167_ == 0)
{
return v_bs_2166_;
}
else
{
lean_object* v_v_2168_; lean_object* v___x_2169_; lean_object* v_bs_x27_2170_; size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v_v_2168_ = lean_array_uget(v_bs_2166_, v_i_2165_);
v___x_2169_ = lean_unsigned_to_nat(0u);
v_bs_x27_2170_ = lean_array_uset(v_bs_2166_, v_i_2165_, v___x_2169_);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2165_, v___x_2171_);
v___x_2173_ = lean_array_uset(v_bs_x27_2170_, v_i_2165_, v_v_2168_);
v_i_2165_ = v___x_2172_;
v_bs_2166_ = v___x_2173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6___boxed(lean_object* v_sz_2175_, lean_object* v_i_2176_, lean_object* v_bs_2177_){
_start:
{
size_t v_sz_boxed_2178_; size_t v_i_boxed_2179_; lean_object* v_res_2180_; 
v_sz_boxed_2178_ = lean_unbox_usize(v_sz_2175_);
lean_dec(v_sz_2175_);
v_i_boxed_2179_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_res_2180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(v_sz_boxed_2178_, v_i_boxed_2179_, v_bs_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(size_t v_sz_2181_, size_t v_i_2182_, lean_object* v_bs_2183_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_usize_dec_lt(v_i_2182_, v_sz_2181_);
if (v___x_2184_ == 0)
{
return v_bs_2183_;
}
else
{
lean_object* v_v_2185_; lean_object* v___x_2186_; lean_object* v_bs_x27_2187_; size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v_v_2185_ = lean_array_uget(v_bs_2183_, v_i_2182_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v_bs_x27_2187_ = lean_array_uset(v_bs_2183_, v_i_2182_, v___x_2186_);
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2182_, v___x_2188_);
v___x_2190_ = lean_array_uset(v_bs_x27_2187_, v_i_2182_, v_v_2185_);
v_i_2182_ = v___x_2189_;
v_bs_2183_ = v___x_2190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4___boxed(lean_object* v_sz_2192_, lean_object* v_i_2193_, lean_object* v_bs_2194_){
_start:
{
size_t v_sz_boxed_2195_; size_t v_i_boxed_2196_; lean_object* v_res_2197_; 
v_sz_boxed_2195_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2196_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(v_sz_boxed_2195_, v_i_boxed_2196_, v_bs_2194_);
return v_res_2197_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__2));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(size_t v_sz_2207_, size_t v_i_2208_, lean_object* v_bs_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v___x_2217_; 
v___x_2217_ = lean_usize_dec_lt(v_i_2208_, v_sz_2207_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_bs_2209_);
return v___x_2218_;
}
else
{
lean_object* v_v_2219_; lean_object* v___x_2220_; 
v_v_2219_ = lean_array_uget_borrowed(v_bs_2209_, v_i_2208_);
v___x_2220_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_v_2219_, v___y_2212_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v_bs_x27_2223_; lean_object* v___x_2224_; lean_object* v___y_2226_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = lean_unsigned_to_nat(0u);
v_bs_x27_2223_ = lean_array_uset(v_bs_2209_, v_i_2208_, v___x_2222_);
v___x_2224_ = l_Lean_LocalDecl_userName(v_a_2221_);
lean_dec(v_a_2221_);
v___x_2255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80));
v___x_2256_ = lean_name_eq(v___x_2224_, v___x_2255_);
if (v___x_2256_ == 0)
{
v___y_2226_ = v___y_2214_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3);
v___x_2258_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_2257_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_dec_ref(v___x_2258_);
v___y_2226_ = v___y_2214_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v___x_2224_);
lean_dec_ref(v_bs_x27_2223_);
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
v___jp_2225_:
{
lean_object* v_ref_2227_; lean_object* v_quotContext_2228_; lean_object* v_currMacroScope_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v_ref_2227_ = lean_ctor_get(v___y_2226_, 5);
v_quotContext_2228_ = lean_ctor_get(v___y_2226_, 10);
v_currMacroScope_2229_ = lean_ctor_get(v___y_2226_, 11);
v___x_2230_ = 0;
v___x_2231_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2230_);
v___x_2232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1));
v___x_2233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc_n(v___x_2231_, 7);
v___x_2234_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2231_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2236_ = lean_mk_syntax_ident(v___x_2224_);
v___x_2237_ = l_Lean_Syntax_node1(v___x_2231_, v___x_2235_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_2239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2231_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4));
lean_inc(v_currMacroScope_2229_);
lean_inc(v_quotContext_2228_);
v___x_2242_ = l_Lean_addMacroScope(v_quotContext_2228_, v___x_2241_, v_currMacroScope_2229_);
v___x_2243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35));
v___x_2244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2231_);
lean_ctor_set(v___x_2244_, 1, v___x_2240_);
lean_ctor_set(v___x_2244_, 2, v___x_2242_);
lean_ctor_set(v___x_2244_, 3, v___x_2243_);
v___x_2245_ = l_Lean_Syntax_node2(v___x_2231_, v___x_2235_, v___x_2239_, v___x_2244_);
v___x_2246_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_2247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2231_);
lean_ctor_set(v___x_2247_, 1, v___x_2235_);
lean_ctor_set(v___x_2247_, 2, v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_2249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2231_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_Syntax_node5(v___x_2231_, v___x_2232_, v___x_2234_, v___x_2237_, v___x_2245_, v___x_2247_, v___x_2249_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_add(v_i_2208_, v___x_2251_);
v___x_2253_ = lean_array_uset(v_bs_x27_2223_, v_i_2208_, v___x_2250_);
v_i_2208_ = v___x_2252_;
v_bs_2209_ = v___x_2253_;
goto _start;
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_bs_2209_);
v_a_2267_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2220_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2220_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___boxed(lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_bs_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
size_t v_sz_boxed_2285_; size_t v_i_boxed_2286_; lean_object* v_res_2287_; 
v_sz_boxed_2285_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(v_sz_boxed_2285_, v_i_boxed_2286_, v_bs_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2287_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__10));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1(lean_object* v_v_2317_, lean_object* v___f_2318_, lean_object* v___x_2319_, lean_object* v___x_2320_, lean_object* v_argVars_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
if (lean_obj_tag(v_v_2317_) == 1)
{
lean_object* v_str_2330_; size_t v_sz_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v_str_2330_ = lean_ctor_get(v_v_2317_, 1);
lean_inc_ref(v_str_2330_);
lean_dec_ref(v_v_2317_);
v_sz_2331_ = lean_array_size(v_argVars_2321_);
v___x_2332_ = ((size_t)0ULL);
lean_inc_ref(v_argVars_2321_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(v_sz_2331_, v___x_2332_, v_argVars_2321_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v_ref_2335_; lean_object* v_quotContext_2336_; lean_object* v_currMacroScope_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; size_t v_sz_2350_; lean_object* v___x_2351_; size_t v_sz_2352_; lean_object* v___x_2353_; size_t v_sz_2354_; lean_object* v___x_2355_; size_t v_sz_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v_ref_2335_ = lean_ctor_get(v___y_2327_, 5);
v_quotContext_2336_ = lean_ctor_get(v___y_2327_, 10);
v_currMacroScope_2337_ = lean_ctor_get(v___y_2327_, 11);
v___x_2338_ = 0;
v___x_2339_ = l_Lean_SourceInfo_fromRef(v_ref_2335_, v___x_2338_);
v___x_2340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0));
v___x_2341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2));
v___x_2342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1));
v___x_2343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
lean_inc_n(v___x_2339_, 3);
v___x_2345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2339_);
lean_ctor_set(v___x_2345_, 1, v___x_2343_);
lean_ctor_set(v___x_2345_, 2, v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__2));
v___x_2347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2339_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
lean_inc_ref_n(v___x_2345_, 7);
v___x_2349_ = l_Lean_Syntax_node7(v___x_2339_, v___x_2348_, v___x_2345_, v___x_2345_, v___x_2345_, v___x_2345_, v___x_2345_, v___x_2345_, v___x_2345_);
v_sz_2350_ = lean_array_size(v_a_2334_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(v_sz_2350_, v___x_2332_, v_a_2334_);
v_sz_2352_ = lean_array_size(v___x_2351_);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(v_sz_2352_, v___x_2332_, v___x_2351_);
v_sz_2354_ = lean_array_size(v___x_2353_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(v_sz_2354_, v___x_2332_, v___x_2353_);
v_sz_2356_ = lean_array_size(v___x_2355_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_2356_, v___x_2332_, v___x_2355_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(v_sz_2331_, v___x_2332_, v_argVars_2321_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; size_t v_sz_2360_; lean_object* v___x_2361_; size_t v_sz_2362_; lean_object* v___x_2363_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v_sz_2360_ = lean_array_size(v_a_2359_);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(v_sz_2360_, v___x_2332_, v_a_2359_);
v_sz_2362_ = lean_array_size(v___x_2361_);
lean_inc_ref(v___x_2361_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(v_sz_2362_, v___x_2332_, v___x_2361_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2363_);
lean_inc_ref(v___f_2318_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc(v___y_2326_);
lean_inc_ref(v___y_2325_);
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
v___x_2365_ = lean_apply_7(v___f_2318_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, lean_box(0));
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc_n(v_a_2366_, 20);
lean_dec_ref(v___x_2365_);
v___x_2367_ = l_Array_append___redArg(v___x_2344_, v___x_2357_);
lean_dec_ref(v___x_2357_);
lean_inc_n(v___x_2339_, 5);
v___x_2368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2339_);
lean_ctor_set(v___x_2368_, 1, v___x_2343_);
lean_ctor_set(v___x_2368_, 2, v___x_2367_);
v___x_2369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_2370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2339_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15);
v___x_2372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_2373_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
lean_inc_n(v_currMacroScope_2337_, 3);
lean_inc_n(v_quotContext_2336_, 3);
v___x_2374_ = l_Lean_addMacroScope(v_quotContext_2336_, v___x_2373_, v_currMacroScope_2337_);
v___x_2375_ = lean_box(0);
lean_inc(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2339_);
lean_ctor_set(v___x_2376_, 1, v___x_2371_);
lean_ctor_set(v___x_2376_, 2, v___x_2374_);
lean_ctor_set(v___x_2376_, 3, v___x_2375_);
v___x_2377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10));
v___x_2378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_2379_ = l_Lean_Syntax_node2(v___x_2339_, v___x_2378_, v___x_2370_, v___x_2376_);
v___x_2380_ = l_Lean_Syntax_node1(v___x_2339_, v___x_2343_, v___x_2379_);
v___x_2381_ = lean_box(0);
v___x_2382_ = l_Lean_Name_str___override(v___x_2381_, v_str_2330_);
v___x_2383_ = lean_mk_syntax_ident(v___x_2382_);
v___x_2384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23));
v___x_2385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4));
v___x_2386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_a_2366_);
lean_ctor_set(v___x_2386_, 1, v___x_2346_);
v___x_2387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6));
v___x_2389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32));
v___x_2390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_a_2366_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
lean_inc(v___x_2383_);
v___x_2391_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2388_, v___x_2390_, v___x_2383_);
v___x_2392_ = l_Array_append___redArg(v___x_2344_, v___x_2361_);
lean_inc_ref(v___x_2392_);
v___x_2393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2393_, 0, v_a_2366_);
lean_ctor_set(v___x_2393_, 1, v___x_2343_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
lean_inc(v___x_2391_);
v___x_2394_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2387_, v___x_2391_, v___x_2393_);
v___x_2395_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2343_, v___x_2394_);
v___x_2396_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2343_, v___x_2395_);
v___x_2397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__7));
v___x_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_a_2366_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100));
v___x_2400_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101));
v___x_2401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_a_2366_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103);
v___x_2403_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104));
v___x_2404_ = l_Lean_addMacroScope(v_quotContext_2336_, v___x_2403_, v_currMacroScope_2337_);
v___x_2405_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107));
v___x_2406_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2406_, 0, v_a_2366_);
lean_ctor_set(v___x_2406_, 1, v___x_2402_);
lean_ctor_set(v___x_2406_, 2, v___x_2404_);
lean_ctor_set(v___x_2406_, 3, v___x_2405_);
v___x_2407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9));
v___x_2408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
v___x_2409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
v___x_2410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_a_2366_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
v___x_2412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56);
v___x_2413_ = l_Lean_addMacroScope(v_quotContext_2336_, v___x_2381_, v_currMacroScope_2337_);
v___x_2414_ = l_Lean_Name_mkStr3(v___x_2340_, v___x_2384_, v___x_2319_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
v___x_2416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60));
lean_inc_ref_n(v___x_2320_, 2);
v___x_2417_ = l_Lean_Name_mkStr3(v___x_2340_, v___x_2320_, v___x_2377_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
v___x_2419_ = l_Lean_Name_mkStr3(v___x_2340_, v___x_2320_, v___x_2341_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
v___x_2421_ = l_Lean_Name_mkStr2(v___x_2340_, v___x_2320_);
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57));
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2420_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2418_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2416_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2415_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
lean_inc_ref(v___x_2428_);
lean_inc(v___x_2413_);
v___x_2429_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2366_);
lean_ctor_set(v___x_2429_, 1, v___x_2412_);
lean_ctor_set(v___x_2429_, 2, v___x_2413_);
lean_ctor_set(v___x_2429_, 3, v___x_2428_);
v___x_2430_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2411_, v___x_2429_);
v___x_2431_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2408_, v___x_2410_, v___x_2430_);
v___x_2432_ = l_Array_append___redArg(v___x_2344_, v_a_2364_);
lean_dec(v_a_2364_);
v___x_2433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2366_);
lean_ctor_set(v___x_2433_, 1, v___x_2343_);
lean_ctor_set(v___x_2433_, 2, v___x_2432_);
v___x_2434_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2387_, v___x_2391_, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2366_);
lean_ctor_set(v___x_2435_, 1, v___x_2369_);
v___x_2436_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2366_);
lean_ctor_set(v___x_2436_, 1, v___x_2371_);
lean_ctor_set(v___x_2436_, 2, v___x_2374_);
lean_ctor_set(v___x_2436_, 3, v___x_2375_);
v___x_2437_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2343_, v___x_2436_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(v_sz_2362_, v___x_2332_, v___x_2361_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc(v___y_2326_);
lean_inc_ref(v___y_2325_);
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2323_);
v___x_2440_ = lean_apply_7(v___f_2318_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, lean_box(0));
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2482_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2482_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2482_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc_n(v_a_2366_, 6);
v___x_2446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2366_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node5(v_a_2366_, v___x_2407_, v___x_2431_, v___x_2434_, v___x_2435_, v___x_2437_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2343_, v___x_2447_);
v___x_2449_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2387_, v___x_2406_, v___x_2448_);
v___x_2450_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2343_, v___x_2449_);
lean_inc(v___x_2339_);
v___x_2451_ = l_Lean_Syntax_node2(v___x_2339_, v___x_2372_, v___x_2368_, v___x_2380_);
v___x_2452_ = l_Lean_Syntax_node2(v_a_2366_, v___x_2399_, v___x_2401_, v___x_2450_);
lean_inc(v___x_2383_);
v___x_2453_ = l_Lean_Syntax_node5(v___x_2339_, v___x_2342_, v___x_2345_, v___x_2347_, v___x_2349_, v___x_2383_, v___x_2451_);
v___x_2454_ = l_Lean_Syntax_node4(v_a_2366_, v___x_2385_, v___x_2386_, v___x_2396_, v___x_2398_, v___x_2452_);
lean_inc_n(v_a_2441_, 19);
v___x_2455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_a_2441_);
lean_ctor_set(v___x_2455_, 1, v___x_2346_);
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_a_2441_);
lean_ctor_set(v___x_2456_, 1, v___x_2389_);
v___x_2457_ = l_Lean_Syntax_node2(v_a_2441_, v___x_2388_, v___x_2456_, v___x_2383_);
v___x_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2458_, 0, v_a_2441_);
lean_ctor_set(v___x_2458_, 1, v___x_2343_);
lean_ctor_set(v___x_2458_, 2, v___x_2392_);
lean_inc(v___x_2457_);
v___x_2459_ = l_Lean_Syntax_node2(v_a_2441_, v___x_2387_, v___x_2457_, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node1(v_a_2441_, v___x_2343_, v___x_2459_);
v___x_2461_ = l_Lean_Syntax_node1(v_a_2441_, v___x_2343_, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2441_);
lean_ctor_set(v___x_2462_, 1, v___x_2397_);
v___x_2463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_a_2441_);
lean_ctor_set(v___x_2463_, 1, v___x_2400_);
v___x_2464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
v___x_2465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2441_);
lean_ctor_set(v___x_2465_, 1, v___x_2409_);
v___x_2466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2466_, 0, v_a_2441_);
lean_ctor_set(v___x_2466_, 1, v___x_2412_);
lean_ctor_set(v___x_2466_, 2, v___x_2413_);
lean_ctor_set(v___x_2466_, 3, v___x_2428_);
v___x_2467_ = l_Lean_Syntax_node1(v_a_2441_, v___x_2411_, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node2(v_a_2441_, v___x_2408_, v___x_2465_, v___x_2467_);
v___x_2469_ = l_Array_append___redArg(v___x_2344_, v_a_2439_);
lean_dec(v_a_2439_);
v___x_2470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2441_);
lean_ctor_set(v___x_2470_, 1, v___x_2343_);
lean_ctor_set(v___x_2470_, 2, v___x_2469_);
v___x_2471_ = l_Lean_Syntax_node2(v_a_2441_, v___x_2387_, v___x_2457_, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2441_);
lean_ctor_set(v___x_2472_, 1, v___x_2445_);
v___x_2473_ = l_Lean_Syntax_node3(v_a_2441_, v___x_2464_, v___x_2468_, v___x_2471_, v___x_2472_);
v___x_2474_ = l_Lean_Syntax_node1(v_a_2441_, v___x_2343_, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node2(v_a_2441_, v___x_2399_, v___x_2463_, v___x_2474_);
v___x_2476_ = l_Lean_Syntax_node4(v_a_2441_, v___x_2385_, v___x_2455_, v___x_2461_, v___x_2462_, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2454_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2453_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2478_);
v___x_2480_ = v___x_2443_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_a_2439_);
lean_dec(v___x_2437_);
lean_dec_ref(v___x_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2431_);
lean_dec_ref(v___x_2428_);
lean_dec(v___x_2413_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2401_);
lean_dec_ref(v___x_2398_);
lean_dec(v___x_2396_);
lean_dec_ref(v___x_2392_);
lean_dec_ref(v___x_2386_);
lean_dec(v___x_2383_);
lean_dec(v___x_2380_);
lean_dec_ref(v___x_2368_);
lean_dec(v_a_2366_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___x_2345_);
lean_dec(v___x_2339_);
v_a_2483_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2440_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2440_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v___x_2437_);
lean_dec_ref(v___x_2435_);
lean_dec(v___x_2434_);
lean_dec(v___x_2431_);
lean_dec_ref(v___x_2428_);
lean_dec(v___x_2413_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2401_);
lean_dec_ref(v___x_2398_);
lean_dec(v___x_2396_);
lean_dec_ref(v___x_2392_);
lean_dec_ref(v___x_2386_);
lean_dec(v___x_2383_);
lean_dec(v___x_2380_);
lean_dec_ref(v___x_2368_);
lean_dec(v_a_2366_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___x_2345_);
lean_dec(v___x_2339_);
lean_dec_ref(v___f_2318_);
v_a_2491_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2438_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2438_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_a_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___x_2357_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___x_2345_);
lean_dec(v___x_2339_);
lean_dec_ref(v_str_2330_);
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2319_);
lean_dec_ref(v___f_2318_);
v_a_2499_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2365_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2365_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___x_2357_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___x_2345_);
lean_dec(v___x_2339_);
lean_dec_ref(v_str_2330_);
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2319_);
lean_dec_ref(v___f_2318_);
v_a_2507_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2363_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2363_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v___x_2357_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___x_2345_);
lean_dec(v___x_2339_);
lean_dec_ref(v_str_2330_);
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2319_);
lean_dec_ref(v___f_2318_);
v_a_2515_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2358_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2358_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_str_2330_);
lean_dec_ref(v_argVars_2321_);
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2319_);
lean_dec_ref(v___f_2318_);
v_a_2523_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2333_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2333_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec_ref(v_argVars_2321_);
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2319_);
lean_dec_ref(v___f_2318_);
v___x_2531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11);
v___x_2532_ = l_Lean_MessageData_ofName(v_v_2317_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_2533_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___boxed(lean_object* v_v_2535_, lean_object* v___f_2536_, lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v_argVars_2539_, lean_object* v_x_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1(v_v_2535_, v___f_2536_, v___x_2537_, v___x_2538_, v_argVars_2539_, v_x_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec_ref(v_x_2540_);
return v_res_2548_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_instMonadEIO(lean_box(0));
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(lean_object* v_msg_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v_toApplicative_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2657_; 
v___x_2564_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0);
v___x_2565_ = l_StateRefT_x27_instMonad___redArg(v___x_2564_);
v_toApplicative_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v___x_2565_, 1);
lean_dec(v_unused_2658_);
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2657_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_toApplicative_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2657_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_toFunctor_2570_; lean_object* v_toSeq_2571_; lean_object* v_toSeqLeft_2572_; lean_object* v_toSeqRight_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2655_; 
v_toFunctor_2570_ = lean_ctor_get(v_toApplicative_2566_, 0);
v_toSeq_2571_ = lean_ctor_get(v_toApplicative_2566_, 2);
v_toSeqLeft_2572_ = lean_ctor_get(v_toApplicative_2566_, 3);
v_toSeqRight_2573_ = lean_ctor_get(v_toApplicative_2566_, 4);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_toApplicative_2566_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v_toApplicative_2566_, 1);
lean_dec(v_unused_2656_);
v___x_2575_ = v_toApplicative_2566_;
v_isShared_2576_ = v_isSharedCheck_2655_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_toSeqRight_2573_);
lean_inc(v_toSeqLeft_2572_);
lean_inc(v_toSeq_2571_);
lean_inc(v_toFunctor_2570_);
lean_dec(v_toApplicative_2566_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2655_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___f_2584_; lean_object* v___x_2586_; 
v___f_2577_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__1));
v___f_2578_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__2));
lean_inc_ref(v_toFunctor_2570_);
v___f_2579_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2579_, 0, v_toFunctor_2570_);
v___f_2580_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2580_, 0, v_toFunctor_2570_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___f_2579_);
lean_ctor_set(v___x_2581_, 1, v___f_2580_);
v___f_2582_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2582_, 0, v_toSeqRight_2573_);
v___f_2583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2583_, 0, v_toSeqLeft_2572_);
v___f_2584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2584_, 0, v_toSeq_2571_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v___f_2582_);
lean_ctor_set(v___x_2575_, 3, v___f_2583_);
lean_ctor_set(v___x_2575_, 2, v___f_2584_);
lean_ctor_set(v___x_2575_, 1, v___f_2577_);
lean_ctor_set(v___x_2575_, 0, v___x_2581_);
v___x_2586_ = v___x_2575_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___f_2577_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v___f_2584_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v___f_2583_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v___f_2582_);
v___x_2586_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___f_2578_);
lean_ctor_set(v___x_2568_, 0, v___x_2586_);
v___x_2588_ = v___x_2568_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___f_2578_);
v___x_2588_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; lean_object* v_toApplicative_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2651_; 
v___x_2589_ = l_StateRefT_x27_instMonad___redArg(v___x_2588_);
v_toApplicative_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2589_, 1);
lean_dec(v_unused_2652_);
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2651_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_toApplicative_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2651_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v_toFunctor_2594_; lean_object* v_toSeq_2595_; lean_object* v_toSeqLeft_2596_; lean_object* v_toSeqRight_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2649_; 
v_toFunctor_2594_ = lean_ctor_get(v_toApplicative_2590_, 0);
v_toSeq_2595_ = lean_ctor_get(v_toApplicative_2590_, 2);
v_toSeqLeft_2596_ = lean_ctor_get(v_toApplicative_2590_, 3);
v_toSeqRight_2597_ = lean_ctor_get(v_toApplicative_2590_, 4);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_toApplicative_2590_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v_toApplicative_2590_, 1);
lean_dec(v_unused_2650_);
v___x_2599_ = v_toApplicative_2590_;
v_isShared_2600_ = v_isSharedCheck_2649_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_toSeqRight_2597_);
lean_inc(v_toSeqLeft_2596_);
lean_inc(v_toSeq_2595_);
lean_inc(v_toFunctor_2594_);
lean_dec(v_toApplicative_2590_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2649_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; lean_object* v___f_2607_; lean_object* v___f_2608_; lean_object* v___x_2610_; 
v___f_2601_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__3));
v___f_2602_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__4));
lean_inc_ref(v_toFunctor_2594_);
v___f_2603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2603_, 0, v_toFunctor_2594_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toFunctor_2594_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___f_2603_);
lean_ctor_set(v___x_2605_, 1, v___f_2604_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toSeqRight_2597_);
v___f_2607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2607_, 0, v_toSeqLeft_2596_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toSeq_2595_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 4, v___f_2606_);
lean_ctor_set(v___x_2599_, 3, v___f_2607_);
lean_ctor_set(v___x_2599_, 2, v___f_2608_);
lean_ctor_set(v___x_2599_, 1, v___f_2601_);
lean_ctor_set(v___x_2599_, 0, v___x_2605_);
v___x_2610_ = v___x_2599_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___f_2601_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v___f_2608_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v___f_2607_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v___f_2606_);
v___x_2610_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2612_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v___f_2602_);
lean_ctor_set(v___x_2592_, 0, v___x_2610_);
v___x_2612_ = v___x_2592_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___f_2602_);
v___x_2612_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v_toApplicative_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2645_; 
v___x_2613_ = l_StateRefT_x27_instMonad___redArg(v___x_2612_);
v_toApplicative_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v___x_2613_, 1);
lean_dec(v_unused_2646_);
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2645_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_toApplicative_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2645_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_toFunctor_2618_; lean_object* v_toSeq_2619_; lean_object* v_toSeqLeft_2620_; lean_object* v_toSeqRight_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2643_; 
v_toFunctor_2618_ = lean_ctor_get(v_toApplicative_2614_, 0);
v_toSeq_2619_ = lean_ctor_get(v_toApplicative_2614_, 2);
v_toSeqLeft_2620_ = lean_ctor_get(v_toApplicative_2614_, 3);
v_toSeqRight_2621_ = lean_ctor_get(v_toApplicative_2614_, 4);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_toApplicative_2614_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v_toApplicative_2614_, 1);
lean_dec(v_unused_2644_);
v___x_2623_ = v_toApplicative_2614_;
v_isShared_2624_ = v_isSharedCheck_2643_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_toSeqRight_2621_);
lean_inc(v_toSeqLeft_2620_);
lean_inc(v_toSeq_2619_);
lean_inc(v_toFunctor_2618_);
lean_dec(v_toApplicative_2614_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2643_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___f_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___x_2634_; 
v___f_2625_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__5));
v___f_2626_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__6));
lean_inc_ref(v_toFunctor_2618_);
v___f_2627_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2627_, 0, v_toFunctor_2618_);
v___f_2628_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2628_, 0, v_toFunctor_2618_);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___f_2627_);
lean_ctor_set(v___x_2629_, 1, v___f_2628_);
v___f_2630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2630_, 0, v_toSeqRight_2621_);
v___f_2631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2631_, 0, v_toSeqLeft_2620_);
v___f_2632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2632_, 0, v_toSeq_2619_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 4, v___f_2630_);
lean_ctor_set(v___x_2623_, 3, v___f_2631_);
lean_ctor_set(v___x_2623_, 2, v___f_2632_);
lean_ctor_set(v___x_2623_, 1, v___f_2625_);
lean_ctor_set(v___x_2623_, 0, v___x_2629_);
v___x_2634_ = v___x_2623_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___f_2625_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v___f_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v___f_2631_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___f_2630_);
v___x_2634_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v___f_2626_);
lean_ctor_set(v___x_2616_, 0, v___x_2634_);
v___x_2636_ = v___x_2616_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___f_2626_);
v___x_2636_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_39090__overap_2639_; lean_object* v___x_2640_; 
v___x_2637_ = lean_box(0);
v___x_2638_ = l_instInhabitedOfMonad___redArg(v___x_2636_, v___x_2637_);
v___x_39090__overap_2639_ = lean_panic_fn_borrowed(v___x_2638_, v_msg_2556_);
lean_dec(v___x_2638_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2561_);
lean_inc(v___y_2560_);
lean_inc_ref(v___y_2559_);
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
v___x_2640_ = lean_apply_7(v___x_39090__overap_2639_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, lean_box(0));
return v___x_2640_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___boxed(lean_object* v_msg_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(v_msg_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2667_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__0));
v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
return v___x_2670_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__2));
v___x_2673_ = l_Lean_stringToMessageData(v___x_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2677_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__6));
v___x_2678_ = lean_unsigned_to_nat(11u);
v___x_2679_ = lean_unsigned_to_nat(122u);
v___x_2680_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__5));
v___x_2681_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__4));
v___x_2682_ = l_mkPanicMessageWithDecl(v___x_2681_, v___x_2680_, v___x_2679_, v___x_2678_, v___x_2677_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(lean_object* v_constName_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2699_; lean_object* v_env_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2699_ = lean_st_ref_get(v___y_2689_);
v_env_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc_ref(v_env_2700_);
lean_dec(v___x_2699_);
v___x_2701_ = 0;
lean_inc(v_constName_2683_);
v___x_2702_ = l_Lean_Environment_findAsync_x3f(v_env_2700_, v_constName_2683_, v___x_2701_);
if (lean_obj_tag(v___x_2702_) == 1)
{
lean_object* v_val_2703_; uint8_t v_kind_2704_; 
v_val_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_val_2703_);
lean_dec_ref(v___x_2702_);
v_kind_2704_ = lean_ctor_get_uint8(v_val_2703_, sizeof(void*)*3);
if (v_kind_2704_ == 6)
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2703_);
if (lean_obj_tag(v___x_2705_) == 6)
{
lean_object* v_val_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_constName_2683_);
v_val_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_val_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 0);
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_val_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v___x_2705_);
v___x_2714_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7);
v___x_2715_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(v___x_2714_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
if (lean_obj_tag(v_a_2716_) == 0)
{
lean_del_object(v___x_2718_);
goto v___jp_2691_;
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2722_; 
lean_dec(v_constName_2683_);
v_val_2720_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_val_2720_);
lean_dec_ref(v_a_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_val_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_val_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_constName_2683_);
v_a_2725_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2715_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2715_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
else
{
lean_dec(v_val_2703_);
goto v___jp_2691_;
}
}
else
{
lean_dec(v___x_2702_);
goto v___jp_2691_;
}
v___jp_2691_:
{
lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2692_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1);
v___x_2693_ = 0;
v___x_2694_ = l_Lean_MessageData_ofConstName(v_constName_2683_, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2692_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_2697_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___boxed(lean_object* v_constName_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(v_constName_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(lean_object* v_params_2743_, size_t v_sz_2744_, size_t v_i_2745_, lean_object* v_bs_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_lt(v_i_2745_, v_sz_2744_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_bs_2746_);
return v___x_2755_;
}
else
{
lean_object* v_v_2756_; lean_object* v___x_2757_; 
v_v_2756_ = lean_array_uget_borrowed(v_bs_2746_, v_i_2745_);
lean_inc(v_v_2756_);
v___x_2757_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(v_v_2756_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v_toConstantVal_2759_; lean_object* v_type_2760_; lean_object* v___x_2761_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref(v___x_2757_);
v_toConstantVal_2759_ = lean_ctor_get(v_a_2758_, 0);
lean_inc_ref(v_toConstantVal_2759_);
lean_dec(v_a_2758_);
v_type_2760_ = lean_ctor_get(v_toConstantVal_2759_, 2);
lean_inc_ref(v_type_2760_);
lean_dec_ref(v_toConstantVal_2759_);
v___x_2761_ = l_Lean_Meta_instantiateForall(v_type_2760_, v_params_2743_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref(v___x_2761_);
v___f_2763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___closed__0));
v___x_2764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0));
v___x_2765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1));
lean_inc(v_v_2756_);
v___f_2766_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2766_, 0, v_v_2756_);
lean_closure_set(v___f_2766_, 1, v___f_2763_);
lean_closure_set(v___f_2766_, 2, v___x_2764_);
lean_closure_set(v___f_2766_, 3, v___x_2765_);
v___x_2767_ = 0;
v___x_2768_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(v_a_2762_, v___f_2766_, v___x_2767_, v___x_2767_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v_bs_x27_2771_; size_t v___x_2772_; size_t v___x_2773_; lean_object* v___x_2774_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = lean_unsigned_to_nat(0u);
v_bs_x27_2771_ = lean_array_uset(v_bs_2746_, v_i_2745_, v___x_2770_);
v___x_2772_ = ((size_t)1ULL);
v___x_2773_ = lean_usize_add(v_i_2745_, v___x_2772_);
v___x_2774_ = lean_array_uset(v_bs_x27_2771_, v_i_2745_, v_a_2769_);
v_i_2745_ = v___x_2773_;
v_bs_2746_ = v___x_2774_;
goto _start;
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_bs_2746_);
v_a_2776_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2768_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2768_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v_bs_2746_);
v_a_2784_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2761_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2761_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_bs_2746_);
v_a_2792_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2757_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2757_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___boxed(lean_object* v_params_2800_, lean_object* v_sz_2801_, lean_object* v_i_2802_, lean_object* v_bs_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
size_t v_sz_boxed_2811_; size_t v_i_boxed_2812_; lean_object* v_res_2813_; 
v_sz_boxed_2811_ = lean_unbox_usize(v_sz_2801_);
lean_dec(v_sz_2801_);
v_i_boxed_2812_ = lean_unbox_usize(v_i_2802_);
lean_dec(v_i_2802_);
v_res_2813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(v_params_2800_, v_sz_boxed_2811_, v_i_boxed_2812_, v_bs_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec_ref(v_params_2800_);
return v_res_2813_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0));
v___x_2827_ = l_String_toRawSubstring_x27(v___x_2826_);
return v___x_2827_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7));
v___x_2836_ = l_String_toRawSubstring_x27(v___x_2835_);
return v___x_2836_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19));
v___x_2866_ = l_String_toRawSubstring_x27(v___x_2865_);
return v___x_2866_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24));
v___x_2874_ = l_String_toRawSubstring_x27(v___x_2873_);
return v___x_2874_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30));
v___x_2886_ = l_Lean_stringToMessageData(v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(lean_object* v_indVal_2887_, lean_object* v_params_2888_, lean_object* v_encInstBinders_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_options_2897_; lean_object* v_inheritedTraceOptions_2898_; uint8_t v_hasTrace_2899_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; 
v_options_2897_ = lean_ctor_get(v_a_2894_, 2);
v_inheritedTraceOptions_2898_ = lean_ctor_get(v_a_2894_, 13);
v_hasTrace_2899_ = lean_ctor_get_uint8(v_options_2897_, sizeof(void*)*1);
if (v_hasTrace_2899_ == 0)
{
v___y_2901_ = v_a_2890_;
v___y_2902_ = v_a_2891_;
v___y_2903_ = v_a_2892_;
v___y_2904_ = v_a_2893_;
v___y_2905_ = v_a_2894_;
v___y_2906_ = v_a_2895_;
goto v___jp_2900_;
}
else
{
lean_object* v_cls_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_cls_3226_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136));
v___x_3227_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139);
v___x_3228_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2898_, v_options_2897_, v___x_3227_);
if (v___x_3228_ == 0)
{
v___y_2901_ = v_a_2890_;
v___y_2902_ = v_a_2891_;
v___y_2903_ = v_a_2892_;
v___y_2904_ = v_a_2893_;
v___y_2905_ = v_a_2894_;
v___y_2906_ = v_a_2895_;
goto v___jp_2900_;
}
else
{
lean_object* v_toConstantVal_3229_; lean_object* v_name_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v_toConstantVal_3229_ = lean_ctor_get(v_indVal_2887_, 0);
v_name_3230_ = lean_ctor_get(v_toConstantVal_3229_, 0);
v___x_3231_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31);
lean_inc(v_name_3230_);
v___x_3232_ = l_Lean_MessageData_ofName(v_name_3230_);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__143);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
lean_inc_ref(v_params_2888_);
v___x_3236_ = lean_array_to_list(v_params_2888_);
v___x_3237_ = lean_box(0);
v___x_3238_ = l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(v___x_3236_, v___x_3237_);
v___x_3239_ = l_Lean_MessageData_ofList(v___x_3238_);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3235_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v_cls_3226_, v___x_3240_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_dec_ref(v___x_3241_);
v___y_2901_ = v_a_2890_;
v___y_2902_ = v_a_2891_;
v___y_2903_ = v_a_2892_;
v___y_2904_ = v_a_2893_;
v___y_2905_ = v_a_2894_;
v___y_2906_ = v_a_2895_;
goto v___jp_2900_;
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v_params_2888_);
lean_dec_ref(v_indVal_2887_);
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
v___jp_2900_:
{
lean_object* v_toConstantVal_2907_; lean_object* v_ctors_2908_; lean_object* v___x_2909_; size_t v_sz_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v_toConstantVal_2907_ = lean_ctor_get(v_indVal_2887_, 0);
lean_inc_ref(v_toConstantVal_2907_);
v_ctors_2908_ = lean_ctor_get(v_indVal_2887_, 4);
lean_inc(v_ctors_2908_);
lean_dec_ref(v_indVal_2887_);
v___x_2909_ = lean_array_mk(v_ctors_2908_);
v_sz_2910_ = lean_array_size(v___x_2909_);
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(v_params_2888_, v_sz_2910_, v___x_2911_, v___x_2909_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_3217_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = l_Array_unzip___redArg(v_a_2913_);
lean_dec(v_a_2913_);
v_fst_2915_ = lean_ctor_get(v___x_2914_, 0);
v_snd_2916_ = lean_ctor_get(v___x_2914_, 1);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_2918_ = v___x_2914_;
v_isShared_2919_ = v_isSharedCheck_3217_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_snd_2916_);
lean_inc(v_fst_2915_);
lean_dec(v___x_2914_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_3217_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v_fst_2921_; lean_object* v_snd_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_3216_; 
v___x_2920_ = l_Array_unzip___redArg(v_snd_2916_);
lean_dec(v_snd_2916_);
v_fst_2921_ = lean_ctor_get(v___x_2920_, 0);
v_snd_2922_ = lean_ctor_get(v___x_2920_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_2924_ = v___x_2920_;
v_isShared_2925_ = v_isSharedCheck_3216_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_snd_2922_);
lean_inc(v_fst_2921_);
lean_dec(v___x_2920_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_3216_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
size_t v_sz_2926_; lean_object* v___x_2927_; 
v_sz_2926_ = lean_array_size(v_params_2888_);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_2926_, v___x_2911_, v_params_2888_, v___y_2903_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_3207_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_3207_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_3207_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v_ref_2932_; lean_object* v_quotContext_2933_; lean_object* v_currMacroScope_2934_; lean_object* v_name_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3204_; 
v_ref_2932_ = lean_ctor_get(v___y_2905_, 5);
v_quotContext_2933_ = lean_ctor_get(v___y_2905_, 10);
v_currMacroScope_2934_ = lean_ctor_get(v___y_2905_, 11);
v_name_2935_ = lean_ctor_get(v_toConstantVal_2907_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_toConstantVal_2907_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; 
v_unused_3205_ = lean_ctor_get(v_toConstantVal_2907_, 2);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_toConstantVal_2907_, 1);
lean_dec(v_unused_3206_);
v___x_2937_ = v_toConstantVal_2907_;
v_isShared_2938_ = v_isSharedCheck_3204_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_name_2935_);
lean_dec(v_toConstantVal_2907_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3204_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2940_ = 0;
v___x_2941_ = l_Lean_SourceInfo_fromRef(v_ref_2932_, v___x_2940_);
v___x_2942_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64));
v___x_2943_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65));
lean_inc(v___x_2941_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 2);
lean_ctor_set(v___x_2924_, 1, v___x_2943_);
lean_ctor_set(v___x_2924_, 0, v___x_2941_);
v___x_2945_ = v___x_2924_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_3203_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; size_t v_sz_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2946_ = l_Lean_mkCIdent(v_name_2935_);
lean_inc_n(v___x_2941_, 2);
v___x_2947_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2942_, v___x_2945_, v___x_2946_);
v___x_2948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2949_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v_sz_2950_ = lean_array_size(v_a_2928_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(v_sz_2950_, v___x_2911_, v_a_2928_);
v___x_2952_ = l_Array_append___redArg(v___x_2949_, v___x_2951_);
lean_dec_ref(v___x_2951_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 1);
lean_ctor_set(v___x_2937_, 2, v___x_2952_);
lean_ctor_set(v___x_2937_, 1, v___x_2948_);
lean_ctor_set(v___x_2937_, 0, v___x_2941_);
v___x_2954_ = v___x_2937_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_3202_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
lean_inc_n(v___x_2941_, 4);
v___x_2955_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2939_, v___x_2947_, v___x_2954_);
v___x_2956_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5));
v___x_2957_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
v___x_2958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2941_);
lean_ctor_set(v___x_2958_, 1, v___x_2948_);
lean_ctor_set(v___x_2958_, 2, v___x_2949_);
lean_inc_ref_n(v___x_2958_, 7);
v___x_2959_ = l_Lean_Syntax_node7(v___x_2941_, v___x_2957_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0));
v___x_2961_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1));
if (v_isShared_2919_ == 0)
{
lean_ctor_set_tag(v___x_2918_, 2);
lean_ctor_set(v___x_2918_, 1, v___x_2960_);
lean_ctor_set(v___x_2918_, 0, v___x_2941_);
v___x_2963_ = v___x_2918_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_2960_);
v___x_2963_ = v_reuseFailAlloc_3201_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; size_t v_sz_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; size_t v_sz_3114_; lean_object* v___x_3115_; size_t v_sz_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; size_t v_sz_3173_; lean_object* v___x_3174_; size_t v_sz_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_2964_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13));
v___x_2965_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15);
v___x_2966_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
lean_inc_n(v_currMacroScope_2934_, 14);
lean_inc_n(v_quotContext_2933_, 14);
v___x_2967_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_2966_, v_currMacroScope_2934_);
v___x_2968_ = lean_box(0);
lean_inc_n(v___x_2941_, 114);
v___x_2969_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2941_);
lean_ctor_set(v___x_2969_, 1, v___x_2965_);
lean_ctor_set(v___x_2969_, 2, v___x_2967_);
lean_ctor_set(v___x_2969_, 3, v___x_2968_);
lean_inc_ref_n(v___x_2958_, 49);
lean_inc_ref(v___x_2969_);
v___x_2970_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2964_, v___x_2969_, v___x_2958_);
v___x_2971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_2972_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2971_, v___x_2958_, v___x_2958_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17));
v___x_2974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2941_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
lean_inc_ref(v___x_2974_);
v___x_2975_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_2974_);
v_sz_2976_ = lean_array_size(v_fst_2915_);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_2976_, v___x_2911_, v_fst_2915_);
v___x_2978_ = l_Array_append___redArg(v___x_2949_, v___x_2977_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2941_);
lean_ctor_set(v___x_2979_, 1, v___x_2948_);
lean_ctor_set(v___x_2979_, 2, v___x_2978_);
v___x_2980_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21));
v___x_2981_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22));
v___x_2982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2941_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24));
v___x_2984_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26);
v___x_2985_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27));
v___x_2986_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_2985_, v_currMacroScope_2934_);
v___x_2987_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32));
v___x_2988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2941_);
lean_ctor_set(v___x_2988_, 1, v___x_2984_);
lean_ctor_set(v___x_2988_, 2, v___x_2986_);
lean_ctor_set(v___x_2988_, 3, v___x_2987_);
v___x_2989_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2983_, v___x_2958_, v___x_2988_);
v___x_2990_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33));
v___x_2991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2941_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35);
v___x_2993_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36));
v___x_2994_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_2993_, v_currMacroScope_2934_);
v___x_2995_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41));
v___x_2996_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2941_);
lean_ctor_set(v___x_2996_, 1, v___x_2992_);
lean_ctor_set(v___x_2996_, 2, v___x_2994_);
lean_ctor_set(v___x_2996_, 3, v___x_2995_);
v___x_2997_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2983_, v___x_2958_, v___x_2996_);
lean_inc_ref(v___x_2991_);
v___x_2998_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2948_, v___x_2989_, v___x_2991_, v___x_2997_);
v___x_2999_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2948_, v___x_2982_, v___x_2998_);
v___x_3000_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2980_, v___x_2999_);
v___x_3001_ = l_Lean_Syntax_node7(v___x_2941_, v___x_2961_, v___x_2963_, v___x_2970_, v___x_2972_, v___x_2975_, v___x_2979_, v___x_2958_, v___x_3000_);
v___x_3002_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2956_, v___x_2959_, v___x_3001_);
v___x_3003_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42));
v___x_3004_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43));
v___x_3005_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44));
v___x_3006_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45));
v___x_3007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_2941_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
v___x_3008_ = l_Array_append___redArg(v___x_2949_, v_encInstBinders_2889_);
v___x_3009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3009_, 0, v___x_2941_);
lean_ctor_set(v___x_3009_, 1, v___x_2948_);
lean_ctor_set(v___x_3009_, 2, v___x_3008_);
v___x_3010_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3006_, v___x_3007_, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_2941_);
lean_ctor_set(v___x_3011_, 1, v___x_3003_);
v___x_3012_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2));
v___x_3013_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3));
v___x_3014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_2941_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
v___x_3015_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3013_, v___x_3014_);
v___x_3016_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3015_);
v___x_3017_ = l_Lean_Syntax_node7(v___x_2941_, v___x_2957_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_2958_, v___x_3016_);
v___x_3018_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46));
v___x_3019_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47));
v___x_3020_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49));
v___x_3021_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3020_, v___x_2958_);
v___x_3022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_2941_);
lean_ctor_set(v___x_3022_, 1, v___x_3018_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51));
v___x_3024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_3025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_3026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_2941_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52);
v___x_3028_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
v___x_3029_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3028_, v_currMacroScope_2934_);
v___x_3030_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56));
v___x_3031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3031_, 0, v___x_2941_);
lean_ctor_set(v___x_3031_, 1, v___x_3027_);
lean_ctor_set(v___x_3031_, 2, v___x_3029_);
lean_ctor_set(v___x_3031_, 3, v___x_3030_);
v___x_3032_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_2955_);
v___x_3033_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2939_, v___x_3031_, v___x_3032_);
lean_inc_ref(v___x_3026_);
v___x_3034_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3024_, v___x_3026_, v___x_3033_);
lean_inc(v___x_3034_);
v___x_3035_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3023_, v___x_2958_, v___x_3034_);
v___x_3036_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67));
v___x_3037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_3038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_2941_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69));
v___x_3040_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70));
v___x_3041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_2941_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72));
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_3044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_3045_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21);
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
v___x_3047_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3046_, v_currMacroScope_2934_);
v___x_3048_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74));
v___x_3049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3049_, 0, v___x_2941_);
lean_ctor_set(v___x_3049_, 1, v___x_3045_);
lean_ctor_set(v___x_3049_, 2, v___x_3047_);
lean_ctor_set(v___x_3049_, 3, v___x_3048_);
v___x_3050_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3044_, v___x_3049_, v___x_2958_);
v___x_3051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_3052_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76);
v___x_3053_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77));
v___x_3054_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3053_, v_currMacroScope_2934_);
v___x_3055_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3055_, 0, v___x_2941_);
lean_ctor_set(v___x_3055_, 1, v___x_3052_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
lean_ctor_set(v___x_3055_, 3, v___x_2968_);
lean_inc_ref(v___x_3055_);
lean_inc_ref_n(v___x_3038_, 5);
v___x_3056_ = l_Lean_Syntax_node3(v___x_2941_, v___x_3051_, v___x_3038_, v___x_2958_, v___x_3055_);
v___x_3057_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2948_, v___x_2958_, v___x_2958_, v___x_3056_);
v___x_3058_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3043_, v___x_3050_, v___x_3057_);
v___x_3059_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37);
v___x_3060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
v___x_3061_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3060_, v_currMacroScope_2934_);
v___x_3062_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79));
v___x_3063_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3063_, 0, v___x_2941_);
lean_ctor_set(v___x_3063_, 1, v___x_3059_);
lean_ctor_set(v___x_3063_, 2, v___x_3061_);
lean_ctor_set(v___x_3063_, 3, v___x_3062_);
v___x_3064_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3044_, v___x_3063_, v___x_2958_);
v___x_3065_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81);
v___x_3066_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82));
v___x_3067_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3066_, v_currMacroScope_2934_);
v___x_3068_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3068_, 0, v___x_2941_);
lean_ctor_set(v___x_3068_, 1, v___x_3065_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
lean_ctor_set(v___x_3068_, 3, v___x_2968_);
lean_inc_ref(v___x_3068_);
v___x_3069_ = l_Lean_Syntax_node3(v___x_2941_, v___x_3051_, v___x_3038_, v___x_2958_, v___x_3068_);
v___x_3070_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2948_, v___x_2958_, v___x_2958_, v___x_3069_);
v___x_3071_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3043_, v___x_3064_, v___x_3070_);
v___x_3072_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2948_, v___x_3058_, v___x_2991_, v___x_3071_);
v___x_3073_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3042_, v___x_3072_);
v___x_3074_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84));
v___x_3075_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3074_, v___x_2958_);
v___x_3076_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85));
v___x_3077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_2941_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_Syntax_node6(v___x_2941_, v___x_3039_, v___x_3041_, v___x_2958_, v___x_3073_, v___x_3075_, v___x_2958_, v___x_3077_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88));
v___x_3080_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3079_, v___x_2958_, v___x_2958_);
v___x_3081_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90));
v___x_3082_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92));
v___x_3083_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94));
v___x_3084_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96));
v___x_3085_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98));
v___x_3086_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3085_, v___x_3055_);
v___x_3087_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4);
v___x_3088_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1));
v___x_3089_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3088_, v_currMacroScope_2934_);
v___x_3090_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3090_, 0, v___x_2941_);
lean_ctor_set(v___x_3090_, 1, v___x_3087_);
lean_ctor_set(v___x_3090_, 2, v___x_3089_);
lean_ctor_set(v___x_3090_, 3, v___x_2968_);
lean_inc_ref(v___x_3090_);
v___x_3091_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3090_);
v___x_3092_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5));
v___x_3093_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6));
v___x_3094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_2941_);
lean_ctor_set(v___x_3094_, 1, v___x_3092_);
v___x_3095_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122));
v___x_3096_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3095_, v___x_2958_);
v___x_3097_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8);
v___x_3098_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9));
v___x_3099_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3098_, v_currMacroScope_2934_);
v___x_3100_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3100_, 0, v___x_2941_);
lean_ctor_set(v___x_3100_, 1, v___x_3097_);
lean_ctor_set(v___x_3100_, 2, v___x_3099_);
lean_ctor_set(v___x_3100_, 3, v___x_2968_);
v___x_3101_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3085_, v___x_3100_);
v___x_3102_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3034_);
lean_inc(v___x_3078_);
v___x_3103_ = l_Lean_Syntax_node5(v___x_2941_, v___x_3084_, v___x_3101_, v___x_2958_, v___x_3102_, v___x_3038_, v___x_3078_);
v___x_3104_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3083_, v___x_3103_);
v___x_3105_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10));
v___x_3106_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11));
v___x_3107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_2941_);
lean_ctor_set(v___x_3107_, 1, v___x_3105_);
v___x_3108_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13));
v___x_3109_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3108_, v___x_2958_, v___x_3090_);
v___x_3110_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3109_);
v___x_3111_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14));
v___x_3112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_2941_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16));
v_sz_3114_ = lean_array_size(v_fst_2921_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(v_sz_3114_, v___x_2911_, v_fst_2921_);
v_sz_3116_ = lean_array_size(v___x_3115_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_3116_, v___x_2911_, v___x_3115_);
v___x_3118_ = l_Array_append___redArg(v___x_2949_, v___x_3117_);
lean_dec_ref(v___x_3117_);
v___x_3119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3119_, 0, v___x_2941_);
lean_ctor_set(v___x_3119_, 1, v___x_2948_);
lean_ctor_set(v___x_3119_, 2, v___x_3118_);
v___x_3120_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3113_, v___x_3119_);
lean_inc_ref(v___x_3112_);
lean_inc_ref(v___x_3107_);
v___x_3121_ = l_Lean_Syntax_node6(v___x_2941_, v___x_3106_, v___x_3107_, v___x_2958_, v___x_2958_, v___x_3110_, v___x_3112_, v___x_3120_);
lean_inc(v___x_3104_);
lean_inc_n(v___x_3096_, 2);
lean_inc_ref(v___x_3094_);
v___x_3122_ = l_Lean_Syntax_node5(v___x_2941_, v___x_3093_, v___x_3094_, v___x_3096_, v___x_3104_, v___x_2958_, v___x_3121_);
v___x_3123_ = l_Lean_Syntax_node5(v___x_2941_, v___x_3084_, v___x_3086_, v___x_3091_, v___x_2958_, v___x_3038_, v___x_3122_);
v___x_3124_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3083_, v___x_3123_);
lean_inc_n(v___x_3080_, 2);
v___x_3125_ = l_Lean_Syntax_node4(v___x_2941_, v___x_3082_, v___x_2958_, v___x_2958_, v___x_3124_, v___x_3080_);
v___x_3126_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3085_, v___x_3068_);
v___x_3127_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110);
v___x_3128_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111));
v___x_3129_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3128_, v_currMacroScope_2934_);
v___x_3130_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3130_, 0, v___x_2941_);
lean_ctor_set(v___x_3130_, 1, v___x_3127_);
lean_ctor_set(v___x_3130_, 2, v___x_3129_);
lean_ctor_set(v___x_3130_, 3, v___x_2968_);
v___x_3131_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3130_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112));
v___x_3133_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113));
v___x_3134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_2941_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
v___x_3135_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115));
v___x_3136_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117));
v___x_3137_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18));
v___x_3138_ = l_Lean_Syntax_node3(v___x_2941_, v___x_3137_, v___x_3094_, v___x_3096_, v___x_3104_);
v___x_3139_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3136_, v___x_3138_, v___x_2958_);
v___x_3140_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119));
v___x_3141_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120));
v___x_3142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_2941_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124));
v___x_3144_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20);
v___x_3145_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21));
v___x_3146_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3145_, v_currMacroScope_2934_);
v___x_3147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3147_, 0, v___x_2941_);
lean_ctor_set(v___x_3147_, 1, v___x_3144_);
lean_ctor_set(v___x_3147_, 2, v___x_3146_);
lean_ctor_set(v___x_3147_, 3, v___x_2968_);
v___x_3148_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3024_, v___x_3026_, v___x_2969_);
v___x_3149_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3148_);
v___x_3150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_3151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_2941_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126));
v___x_3153_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128);
v___x_3154_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129));
v___x_3155_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3154_, v_currMacroScope_2934_);
v___x_3156_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132));
v___x_3157_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3157_, 0, v___x_2941_);
lean_ctor_set(v___x_3157_, 1, v___x_3153_);
lean_ctor_set(v___x_3157_, 2, v___x_3155_);
lean_ctor_set(v___x_3157_, 3, v___x_3156_);
lean_inc(v___x_3131_);
v___x_3158_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2939_, v___x_3157_, v___x_3131_);
v___x_3159_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3152_, v___x_3158_);
lean_inc_ref(v___x_3147_);
v___x_3160_ = l_Lean_Syntax_node4(v___x_2941_, v___x_3143_, v___x_3147_, v___x_3149_, v___x_3151_, v___x_3159_);
v___x_3161_ = l_Lean_Syntax_node4(v___x_2941_, v___x_3140_, v___x_3142_, v___x_2958_, v___x_3096_, v___x_3160_);
v___x_3162_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3136_, v___x_3161_, v___x_2958_);
v___x_3163_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23));
v___x_3164_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25);
v___x_3165_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26));
v___x_3166_ = l_Lean_addMacroScope(v_quotContext_2933_, v___x_3165_, v_currMacroScope_2934_);
v___x_3167_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28));
v___x_3168_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3168_, 0, v___x_2941_);
lean_ctor_set(v___x_3168_, 1, v___x_3164_);
lean_ctor_set(v___x_3168_, 2, v___x_3166_);
lean_ctor_set(v___x_3168_, 3, v___x_3167_);
v___x_3169_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29));
v___x_3170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_2941_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3108_, v___x_2958_, v___x_3147_);
v___x_3172_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3171_);
v_sz_3173_ = lean_array_size(v_snd_2922_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(v_sz_3173_, v___x_2911_, v_snd_2922_);
v_sz_3175_ = lean_array_size(v___x_3174_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_3175_, v___x_2911_, v___x_3174_);
v___x_3177_ = l_Array_append___redArg(v___x_2949_, v___x_3176_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3178_, 0, v___x_2941_);
lean_ctor_set(v___x_3178_, 1, v___x_2948_);
lean_ctor_set(v___x_3178_, 2, v___x_3177_);
v___x_3179_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3113_, v___x_3178_);
v___x_3180_ = l_Lean_Syntax_node6(v___x_2941_, v___x_3106_, v___x_3107_, v___x_2958_, v___x_2958_, v___x_3172_, v___x_3112_, v___x_3179_);
v___x_3181_ = l_Lean_Syntax_node3(v___x_2941_, v___x_3163_, v___x_3168_, v___x_3170_, v___x_3180_);
v___x_3182_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3152_, v___x_3181_);
v___x_3183_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3136_, v___x_3182_, v___x_2958_);
v___x_3184_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2948_, v___x_3139_, v___x_3162_, v___x_3183_);
v___x_3185_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3135_, v___x_3184_);
v___x_3186_ = l_Lean_Syntax_node2(v___x_2941_, v___x_3133_, v___x_3134_, v___x_3185_);
v___x_3187_ = l_Lean_Syntax_node5(v___x_2941_, v___x_3084_, v___x_3126_, v___x_3131_, v___x_2958_, v___x_3038_, v___x_3186_);
v___x_3188_ = l_Lean_Syntax_node1(v___x_2941_, v___x_3083_, v___x_3187_);
v___x_3189_ = l_Lean_Syntax_node4(v___x_2941_, v___x_3082_, v___x_2958_, v___x_2958_, v___x_3188_, v___x_3080_);
v___x_3190_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2948_, v___x_3125_, v___x_2958_, v___x_3189_);
v___x_3191_ = l_Lean_Syntax_node3(v___x_2941_, v___x_3081_, v___x_2974_, v___x_3190_, v___x_2958_);
v___x_3192_ = l_Lean_Syntax_node1(v___x_2941_, v___x_2948_, v___x_3191_);
v___x_3193_ = l_Lean_Syntax_node4(v___x_2941_, v___x_3036_, v___x_3038_, v___x_3078_, v___x_3080_, v___x_3192_);
v___x_3194_ = l_Lean_Syntax_node6(v___x_2941_, v___x_3019_, v___x_3021_, v___x_3022_, v___x_2958_, v___x_2958_, v___x_3035_, v___x_3193_);
v___x_3195_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2956_, v___x_3017_, v___x_3194_);
v___x_3196_ = l_Lean_Syntax_node3(v___x_2941_, v___x_3004_, v___x_3010_, v___x_3011_, v___x_3195_);
v___x_3197_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2948_, v___x_3002_, v___x_3196_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_3197_);
v___x_3199_ = v___x_2930_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_del_object(v___x_2924_);
lean_dec(v_snd_2922_);
lean_dec(v_fst_2921_);
lean_del_object(v___x_2918_);
lean_dec(v_fst_2915_);
lean_dec_ref(v_toConstantVal_2907_);
v_a_3208_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_2927_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_2927_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v_toConstantVal_2907_);
lean_dec_ref(v_params_2888_);
v_a_3218_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_2912_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_2912_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___boxed(lean_object* v_indVal_3250_, lean_object* v_params_3251_, lean_object* v_encInstBinders_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(v_indVal_3250_, v_params_3251_, v_encInstBinders_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
lean_dec(v_a_3254_);
lean_dec_ref(v_a_3253_);
lean_dec_ref(v_encInstBinders_3252_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(size_t v_sz_3261_, size_t v_i_3262_, lean_object* v_bs_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(v_sz_3261_, v_i_3262_, v_bs_3263_, v___y_3268_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___boxed(lean_object* v_sz_3272_, lean_object* v_i_3273_, lean_object* v_bs_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
size_t v_sz_boxed_3282_; size_t v_i_boxed_3283_; lean_object* v_res_3284_; 
v_sz_boxed_3282_ = lean_unbox_usize(v_sz_3272_);
lean_dec(v_sz_3272_);
v_i_boxed_3283_ = lean_unbox_usize(v_i_3273_);
lean_dec(v_i_3273_);
v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(v_sz_boxed_3282_, v_i_boxed_3283_, v_bs_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(size_t v_sz_3285_, size_t v_i_3286_, lean_object* v_bs_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(v_sz_3285_, v_i_3286_, v_bs_3287_, v___y_3292_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___boxed(lean_object* v_sz_3296_, lean_object* v_i_3297_, lean_object* v_bs_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
size_t v_sz_boxed_3306_; size_t v_i_boxed_3307_; lean_object* v_res_3308_; 
v_sz_boxed_3306_ = lean_unbox_usize(v_sz_3296_);
lean_dec(v_sz_3296_);
v_i_boxed_3307_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(v_sz_boxed_3306_, v_i_boxed_3307_, v_bs_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(size_t v_sz_3309_, size_t v_i_3310_, lean_object* v_bs_3311_){
_start:
{
uint8_t v___x_3312_; 
v___x_3312_ = lean_usize_dec_lt(v_i_3310_, v_sz_3309_);
if (v___x_3312_ == 0)
{
return v_bs_3311_;
}
else
{
lean_object* v_v_3313_; lean_object* v___x_3314_; lean_object* v_bs_x27_3315_; size_t v___x_3316_; size_t v___x_3317_; lean_object* v___x_3318_; 
v_v_3313_ = lean_array_uget(v_bs_3311_, v_i_3310_);
v___x_3314_ = lean_unsigned_to_nat(0u);
v_bs_x27_3315_ = lean_array_uset(v_bs_3311_, v_i_3310_, v___x_3314_);
v___x_3316_ = ((size_t)1ULL);
v___x_3317_ = lean_usize_add(v_i_3310_, v___x_3316_);
v___x_3318_ = lean_array_uset(v_bs_x27_3315_, v_i_3310_, v_v_3313_);
v_i_3310_ = v___x_3317_;
v_bs_3311_ = v___x_3318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2___boxed(lean_object* v_sz_3320_, lean_object* v_i_3321_, lean_object* v_bs_3322_){
_start:
{
size_t v_sz_boxed_3323_; size_t v_i_boxed_3324_; lean_object* v_res_3325_; 
v_sz_boxed_3323_ = lean_unbox_usize(v_sz_3320_);
lean_dec(v_sz_3320_);
v_i_boxed_3324_ = lean_unbox_usize(v_i_3321_);
lean_dec(v_i_3321_);
v_res_3325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(v_sz_boxed_3323_, v_i_boxed_3324_, v_bs_3322_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(lean_object* v_as_3326_, size_t v_i_3327_, size_t v_stop_3328_, lean_object* v_b_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_eq(v_i_3327_, v_stop_3328_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_array_uget_borrowed(v_as_3326_, v_i_3327_);
lean_inc(v___x_3336_);
v___x_3337_ = l_Lean_Meta_isType(v___x_3336_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v_a_3340_; uint8_t v___x_3344_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
v___x_3344_ = lean_unbox(v_a_3338_);
lean_dec(v_a_3338_);
if (v___x_3344_ == 0)
{
v_a_3340_ = v_b_3329_;
goto v___jp_3339_;
}
else
{
lean_object* v___x_3345_; 
lean_inc(v___x_3336_);
v___x_3345_ = lean_array_push(v_b_3329_, v___x_3336_);
v_a_3340_ = v___x_3345_;
goto v___jp_3339_;
}
v___jp_3339_:
{
size_t v___x_3341_; size_t v___x_3342_; 
v___x_3341_ = ((size_t)1ULL);
v___x_3342_ = lean_usize_add(v_i_3327_, v___x_3341_);
v_i_3327_ = v___x_3342_;
v_b_3329_ = v_a_3340_;
goto _start;
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v_b_3329_);
v_a_3346_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3337_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3337_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_b_3329_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg___boxed(lean_object* v_as_3355_, lean_object* v_i_3356_, lean_object* v_stop_3357_, lean_object* v_b_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
size_t v_i_boxed_3364_; size_t v_stop_boxed_3365_; lean_object* v_res_3366_; 
v_i_boxed_3364_ = lean_unbox_usize(v_i_3356_);
lean_dec(v_i_3356_);
v_stop_boxed_3365_ = lean_unbox_usize(v_stop_3357_);
lean_dec(v_stop_3357_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_as_3355_, v_i_boxed_3364_, v_stop_boxed_3365_, v_b_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec_ref(v_as_3355_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_bs_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_bs_3386_);
return v___x_3392_;
}
else
{
lean_object* v_v_3393_; lean_object* v___x_3394_; 
v_v_3393_ = lean_array_uget_borrowed(v_bs_3386_, v_i_3385_);
v___x_3394_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_v_3393_, v___y_3387_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v_ref_3396_; lean_object* v_quotContext_3397_; lean_object* v_currMacroScope_3398_; lean_object* v___x_3399_; lean_object* v_bs_x27_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref(v___x_3394_);
v_ref_3396_ = lean_ctor_get(v___y_3388_, 5);
v_quotContext_3397_ = lean_ctor_get(v___y_3388_, 10);
v_currMacroScope_3398_ = lean_ctor_get(v___y_3388_, 11);
v___x_3399_ = lean_unsigned_to_nat(0u);
v_bs_x27_3400_ = lean_array_uset(v_bs_3386_, v_i_3385_, v___x_3399_);
v___x_3401_ = 0;
v___x_3402_ = l_Lean_SourceInfo_fromRef(v_ref_3396_, v___x_3401_);
v___x_3403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1));
v___x_3404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2));
lean_inc_n(v___x_3402_, 6);
v___x_3405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3402_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_3407_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_3408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3402_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
lean_ctor_set(v___x_3408_, 2, v___x_3407_);
v___x_3409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_3410_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52);
v___x_3411_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
lean_inc(v_currMacroScope_3398_);
lean_inc(v_quotContext_3397_);
v___x_3412_ = l_Lean_addMacroScope(v_quotContext_3397_, v___x_3411_, v_currMacroScope_3398_);
v___x_3413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5));
v___x_3414_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3402_);
lean_ctor_set(v___x_3414_, 1, v___x_3410_);
lean_ctor_set(v___x_3414_, 2, v___x_3412_);
lean_ctor_set(v___x_3414_, 3, v___x_3413_);
v___x_3415_ = l_Lean_LocalDecl_userName(v_a_3395_);
lean_dec(v_a_3395_);
v___x_3416_ = lean_mk_syntax_ident(v___x_3415_);
v___x_3417_ = l_Lean_Syntax_node1(v___x_3402_, v___x_3406_, v___x_3416_);
v___x_3418_ = l_Lean_Syntax_node2(v___x_3402_, v___x_3409_, v___x_3414_, v___x_3417_);
v___x_3419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6));
v___x_3420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3402_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_Syntax_node4(v___x_3402_, v___x_3403_, v___x_3405_, v___x_3408_, v___x_3418_, v___x_3420_);
v___x_3422_ = ((size_t)1ULL);
v___x_3423_ = lean_usize_add(v_i_3385_, v___x_3422_);
v___x_3424_ = lean_array_uset(v_bs_x27_3400_, v_i_3385_, v___x_3421_);
v_i_3385_ = v___x_3423_;
v_bs_3386_ = v___x_3424_;
goto _start;
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v_bs_3386_);
v_a_3426_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3394_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3394_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___boxed(lean_object* v_sz_3434_, lean_object* v_i_3435_, lean_object* v_bs_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
size_t v_sz_boxed_3441_; size_t v_i_boxed_3442_; lean_object* v_res_3443_; 
v_sz_boxed_3441_ = lean_unbox_usize(v_sz_3434_);
lean_dec(v_sz_3434_);
v_i_boxed_3442_ = lean_unbox_usize(v_i_3435_);
lean_dec(v_i_3435_);
v_res_3443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(v_sz_boxed_3441_, v_i_boxed_3442_, v_bs_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec_ref(v___y_3437_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(lean_object* v___x_3444_, lean_object* v_a_3445_, lean_object* v___x_3446_, lean_object* v_params_3447_, lean_object* v_x_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_a_3457_; lean_object* v___y_3480_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = lean_array_get_size(v_params_3447_);
v___x_3491_ = lean_mk_empty_array_with_capacity(v___x_3446_);
v___x_3492_ = lean_nat_dec_lt(v___x_3446_, v___x_3490_);
if (v___x_3492_ == 0)
{
v_a_3457_ = v___x_3491_;
goto v___jp_3456_;
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_nat_dec_le(v___x_3490_, v___x_3490_);
if (v___x_3493_ == 0)
{
if (v___x_3492_ == 0)
{
v_a_3457_ = v___x_3491_;
goto v___jp_3456_;
}
else
{
size_t v___x_3494_; size_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = lean_usize_of_nat(v___x_3490_);
v___x_3496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_params_3447_, v___x_3494_, v___x_3495_, v___x_3491_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
v___y_3480_ = v___x_3496_;
goto v___jp_3479_;
}
}
else
{
size_t v___x_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = lean_usize_of_nat(v___x_3490_);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_params_3447_, v___x_3497_, v___x_3498_, v___x_3491_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
v___y_3480_ = v___x_3499_;
goto v___jp_3479_;
}
}
v___jp_3456_:
{
size_t v_sz_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v_sz_3458_ = lean_array_size(v_a_3457_);
v___x_3459_ = ((size_t)0ULL);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(v_sz_3458_, v___x_3459_, v_a_3457_, v___y_3451_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; lean_object* v_env_3463_; uint8_t v___x_3464_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref(v___x_3460_);
v___x_3462_ = lean_st_ref_get(v___y_3454_);
v_env_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc_ref(v_env_3463_);
lean_dec(v___x_3462_);
v___x_3464_ = l_Lean_isStructure(v_env_3463_, v___x_3444_);
if (v___x_3464_ == 0)
{
size_t v_sz_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_sz_3465_ = lean_array_size(v_a_3461_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(v_sz_3465_, v___x_3459_, v_a_3461_);
v___x_3467_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(v_a_3445_, v_params_3447_, v___x_3466_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec_ref(v___x_3466_);
return v___x_3467_;
}
else
{
size_t v_sz_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_sz_3468_ = lean_array_size(v_a_3461_);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(v_sz_3468_, v___x_3459_, v_a_3461_);
v___x_3470_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(v_a_3445_, v_params_3447_, v___x_3469_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec_ref(v___x_3469_);
return v___x_3470_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v_params_3447_);
lean_dec_ref(v_a_3445_);
lean_dec(v___x_3444_);
v_a_3471_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3460_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3460_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
v___jp_3479_:
{
if (lean_obj_tag(v___y_3480_) == 0)
{
lean_object* v_a_3481_; 
v_a_3481_ = lean_ctor_get(v___y_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___y_3480_);
v_a_3457_ = v_a_3481_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_params_3447_);
lean_dec_ref(v_a_3445_);
lean_dec(v___x_3444_);
v_a_3482_ = lean_ctor_get(v___y_3480_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___y_3480_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___y_3480_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___y_3480_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed(lean_object* v___x_3500_, lean_object* v_a_3501_, lean_object* v___x_3502_, lean_object* v_params_3503_, lean_object* v_x_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(v___x_3500_, v_a_3501_, v___x_3502_, v_params_3503_, v_x_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v_x_3504_);
lean_dec(v___x_3502_);
return v_res_3512_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3513_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0);
v___x_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1);
v___x_3517_ = lean_unsigned_to_nat(0u);
v___x_3518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
lean_ctor_set(v___x_3518_, 2, v___x_3517_);
lean_ctor_set(v___x_3518_, 3, v___x_3517_);
lean_ctor_set(v___x_3518_, 4, v___x_3516_);
lean_ctor_set(v___x_3518_, 5, v___x_3516_);
lean_ctor_set(v___x_3518_, 6, v___x_3516_);
lean_ctor_set(v___x_3518_, 7, v___x_3516_);
lean_ctor_set(v___x_3518_, 8, v___x_3516_);
lean_ctor_set(v___x_3518_, 9, v___x_3516_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = lean_unsigned_to_nat(32u);
v___x_3520_ = lean_mk_empty_array_with_capacity(v___x_3519_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3522_ = ((size_t)5ULL);
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = lean_unsigned_to_nat(32u);
v___x_3525_ = lean_mk_empty_array_with_capacity(v___x_3524_);
v___x_3526_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3);
v___x_3527_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___x_3525_);
lean_ctor_set(v___x_3527_, 2, v___x_3523_);
lean_ctor_set(v___x_3527_, 3, v___x_3523_);
lean_ctor_set_usize(v___x_3527_, 4, v___x_3522_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3528_ = lean_box(1);
v___x_3529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4);
v___x_3530_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1);
v___x_3531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
lean_ctor_set(v___x_3531_, 2, v___x_3528_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(lean_object* v_msgData_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; lean_object* v_env_3536_; lean_object* v___x_3537_; lean_object* v_scopes_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v_opts_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3535_ = lean_st_ref_get(v___y_3533_);
v_env_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc_ref(v_env_3536_);
lean_dec(v___x_3535_);
v___x_3537_ = lean_st_ref_get(v___y_3533_);
v_scopes_3538_ = lean_ctor_get(v___x_3537_, 2);
lean_inc(v_scopes_3538_);
lean_dec(v___x_3537_);
v___x_3539_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3540_ = l_List_head_x21___redArg(v___x_3539_, v_scopes_3538_);
lean_dec(v_scopes_3538_);
v_opts_3541_ = lean_ctor_get(v___x_3540_, 1);
lean_inc_ref(v_opts_3541_);
lean_dec(v___x_3540_);
v___x_3542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2);
v___x_3543_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5);
v___x_3544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3544_, 0, v_env_3536_);
lean_ctor_set(v___x_3544_, 1, v___x_3542_);
lean_ctor_set(v___x_3544_, 2, v___x_3543_);
lean_ctor_set(v___x_3544_, 3, v_opts_3541_);
v___x_3545_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v_msgData_3532_);
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___boxed(lean_object* v_msgData_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(v_msgData_3547_, v___y_3548_);
lean_dec(v___y_3548_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(lean_object* v_msgData_3551_, lean_object* v_macroStack_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; lean_object* v_scopes_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_opts_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3555_ = lean_st_ref_get(v___y_3553_);
v_scopes_3556_ = lean_ctor_get(v___x_3555_, 2);
lean_inc(v_scopes_3556_);
lean_dec(v___x_3555_);
v___x_3557_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3558_ = l_List_head_x21___redArg(v___x_3557_, v_scopes_3556_);
lean_dec(v_scopes_3556_);
v_opts_3559_ = lean_ctor_get(v___x_3558_, 1);
lean_inc_ref(v_opts_3559_);
lean_dec(v___x_3558_);
v___x_3560_ = l_Lean_Elab_pp_macroStack;
v___x_3561_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2(v_opts_3559_, v___x_3560_);
lean_dec_ref(v_opts_3559_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_dec(v_macroStack_3552_);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_msgData_3551_);
return v___x_3562_;
}
else
{
if (lean_obj_tag(v_macroStack_3552_) == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_msgData_3551_);
return v___x_3563_;
}
else
{
lean_object* v_head_3564_; lean_object* v_after_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3580_; 
v_head_3564_ = lean_ctor_get(v_macroStack_3552_, 0);
lean_inc(v_head_3564_);
v_after_3565_ = lean_ctor_get(v_head_3564_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_head_3564_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_head_3564_, 0);
lean_dec(v_unused_3581_);
v___x_3567_ = v_head_3564_;
v_isShared_3568_ = v_isSharedCheck_3580_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_after_3565_);
lean_dec(v_head_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3580_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3569_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_3568_ == 0)
{
lean_ctor_set_tag(v___x_3567_, 7);
lean_ctor_set(v___x_3567_, 1, v___x_3569_);
lean_ctor_set(v___x_3567_, 0, v_msgData_3551_);
v___x_3571_ = v___x_3567_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_msgData_3551_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v_msgData_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3572_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = l_Lean_MessageData_ofSyntax(v_after_3565_);
v___x_3575_ = l_Lean_indentD(v___x_3574_);
v_msgData_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3576_, 0, v___x_3573_);
lean_ctor_set(v_msgData_3576_, 1, v___x_3575_);
v___x_3577_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3(v_msgData_3576_, v_macroStack_3552_);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg___boxed(lean_object* v_msgData_3582_, lean_object* v_macroStack_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(v_msgData_3582_, v_macroStack_3583_, v___y_3584_);
lean_dec(v___y_3584_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(lean_object* v_msg_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_Elab_Command_getRef___redArg(v___y_3588_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v_macroStack_3593_; lean_object* v___x_3594_; lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3606_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref(v___x_3591_);
v_macroStack_3593_ = lean_ctor_get(v___y_3588_, 4);
v___x_3594_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(v_msg_3587_, v___y_3589_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
lean_inc_n(v_macroStack_3593_, 2);
v___x_3596_ = l_Lean_Elab_getBetterRef(v_a_3592_, v_macroStack_3593_);
lean_dec(v_a_3592_);
v___x_3597_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(v_a_3595_, v_macroStack_3593_, v___y_3589_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3596_);
lean_ctor_set(v___x_3602_, 1, v_a_3598_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 1);
lean_ctor_set(v___x_3600_, 0, v___x_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v_msg_3587_);
v_a_3607_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3591_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3591_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg___boxed(lean_object* v_msg_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v_msg_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3619_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0));
v___x_3622_ = l_Lean_stringToMessageData(v___x_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(lean_object* v_constName_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; lean_object* v_env_3628_; lean_object* v___x_3629_; 
v___x_3627_ = lean_st_ref_get(v___y_3625_);
v_env_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc_ref(v_env_3628_);
lean_dec(v___x_3627_);
lean_inc(v_constName_3623_);
v___x_3629_ = l_Lean_isInductiveCore_x3f(v_env_3628_, v_constName_3623_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v___x_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3630_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1);
v___x_3631_ = 0;
v___x_3632_ = l_Lean_MessageData_ofConstName(v_constName_3623_, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3630_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3633_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v___x_3635_, v___y_3624_, v___y_3625_);
return v___x_3636_;
}
else
{
lean_object* v_val_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_constName_3623_);
v_val_3637_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3629_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_val_3637_);
lean_dec(v___x_3629_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 0);
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_val_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___boxed(lean_object* v_constName_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(v_constName_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3649_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(lean_object* v_declNames_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3660_ = lean_array_get_size(v_declNames_3656_);
v___x_3661_ = lean_unsigned_to_nat(1u);
v___x_3662_ = lean_nat_dec_eq(v___x_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_box(v___x_3662_);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = lean_array_fget_borrowed(v_declNames_3656_, v___x_3665_);
lean_inc(v___x_3666_);
v___x_3667_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(v___x_3666_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v_toConstantVal_3669_; lean_object* v_numIndices_3670_; lean_object* v_all_3671_; lean_object* v___f_3672_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3667_);
v_toConstantVal_3669_ = lean_ctor_get(v_a_3668_, 0);
lean_inc_ref(v_toConstantVal_3669_);
v_numIndices_3670_ = lean_ctor_get(v_a_3668_, 2);
lean_inc(v_numIndices_3670_);
v_all_3671_ = lean_ctor_get(v_a_3668_, 3);
lean_inc(v_all_3671_);
lean_inc(v___x_3666_);
v___f_3672_ = lean_alloc_closure((void*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3672_, 0, v___x_3666_);
lean_closure_set(v___f_3672_, 1, v_a_3668_);
lean_closure_set(v___f_3672_, 2, v___x_3665_);
v___x_3723_ = l_List_lengthTR___redArg(v_all_3671_);
lean_dec(v_all_3671_);
v___x_3724_ = lean_nat_dec_eq(v___x_3723_, v___x_3661_);
lean_dec(v___x_3723_);
if (v___x_3724_ == 0)
{
if (v___x_3662_ == 0)
{
v___y_3710_ = v_a_3657_;
v___y_3711_ = v_a_3658_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec_ref(v___f_3672_);
lean_dec(v_numIndices_3670_);
lean_dec_ref(v_toConstantVal_3669_);
v___x_3725_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3);
v___x_3726_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v___x_3725_, v_a_3657_, v_a_3658_);
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
v___y_3710_ = v_a_3657_;
v___y_3711_ = v_a_3658_;
goto v___jp_3709_;
}
v___jp_3673_:
{
lean_object* v_type_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_type_3676_ = lean_ctor_get(v_toConstantVal_3669_, 2);
lean_inc_ref(v_type_3676_);
lean_dec_ref(v_toConstantVal_3669_);
v___x_3677_ = 0;
v___x_3678_ = lean_box(v___x_3677_);
v___x_3679_ = lean_box(v___x_3677_);
v___x_3680_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed), 12, 5);
lean_closure_set(v___x_3680_, 0, lean_box(0));
lean_closure_set(v___x_3680_, 1, v_type_3676_);
lean_closure_set(v___x_3680_, 2, v___f_3672_);
lean_closure_set(v___x_3680_, 3, v___x_3678_);
lean_closure_set(v___x_3680_, 4, v___x_3679_);
v___x_3681_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_3680_, v___y_3674_, v___y_3675_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
v___x_3683_ = l_Lean_Elab_Command_elabCommand(v_a_3682_, v___y_3674_, v___y_3675_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3691_; 
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; 
v_unused_3692_ = lean_ctor_get(v___x_3683_, 0);
lean_dec(v_unused_3692_);
v___x_3685_ = v___x_3683_;
v_isShared_3686_ = v_isSharedCheck_3691_;
goto v_resetjp_3684_;
}
else
{
lean_dec(v___x_3683_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3691_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3687_ = lean_box(v___x_3662_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3687_);
v___x_3689_ = v___x_3685_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3683_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3683_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
v_a_3701_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3681_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3681_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
v___jp_3709_:
{
uint8_t v___x_3712_; 
v___x_3712_ = lean_nat_dec_eq(v_numIndices_3670_, v___x_3665_);
lean_dec(v_numIndices_3670_);
if (v___x_3712_ == 0)
{
if (v___x_3662_ == 0)
{
v___y_3674_ = v___y_3710_;
v___y_3675_ = v___y_3711_;
goto v___jp_3673_;
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec_ref(v___f_3672_);
lean_dec_ref(v_toConstantVal_3669_);
v___x_3713_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1);
v___x_3714_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v___x_3713_, v___y_3710_, v___y_3711_);
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
v___y_3674_ = v___y_3710_;
v___y_3675_ = v___y_3711_;
goto v___jp_3673_;
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_a_3735_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3667_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3667_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed(lean_object* v_declNames_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(v_declNames_3743_, v_a_3744_, v_a_3745_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec_ref(v_declNames_3743_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(size_t v_sz_3748_, size_t v_i_3749_, lean_object* v_bs_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(v_sz_3748_, v_i_3749_, v_bs_3750_, v___y_3753_, v___y_3755_, v___y_3756_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___boxed(lean_object* v_sz_3759_, lean_object* v_i_3760_, lean_object* v_bs_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
size_t v_sz_boxed_3769_; size_t v_i_boxed_3770_; lean_object* v_res_3771_; 
v_sz_boxed_3769_ = lean_unbox_usize(v_sz_3759_);
lean_dec(v_sz_3759_);
v_i_boxed_3770_ = lean_unbox_usize(v_i_3760_);
lean_dec(v_i_3760_);
v_res_3771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(v_sz_boxed_3769_, v_i_boxed_3770_, v_bs_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(lean_object* v_as_3772_, size_t v_i_3773_, size_t v_stop_3774_, lean_object* v_b_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_as_3772_, v_i_3773_, v_stop_3774_, v_b_3775_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___boxed(lean_object* v_as_3784_, lean_object* v_i_3785_, lean_object* v_stop_3786_, lean_object* v_b_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
size_t v_i_boxed_3795_; size_t v_stop_boxed_3796_; lean_object* v_res_3797_; 
v_i_boxed_3795_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_stop_boxed_3796_ = lean_unbox_usize(v_stop_3786_);
lean_dec(v_stop_3786_);
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(v_as_3784_, v_i_boxed_3795_, v_stop_boxed_3796_, v_b_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v_as_3784_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(lean_object* v_msgData_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(v_msgData_3798_, v___y_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___boxed(lean_object* v_msgData_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(v_msgData_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(lean_object* v_00_u03b1_3808_, lean_object* v_msg_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v_msg_3809_, v___y_3810_, v___y_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___boxed(lean_object* v_00_u03b1_3814_, lean_object* v_msg_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(v_00_u03b1_3814_, v_msg_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(lean_object* v_msgData_3820_, lean_object* v_macroStack_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(v_msgData_3820_, v_macroStack_3821_, v___y_3823_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___boxed(lean_object* v_msgData_3826_, lean_object* v_macroStack_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(v_msgData_3826_, v_macroStack_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57));
v___x_3898_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_));
v___x_3899_ = l_Lean_Elab_registerDerivingHandler(v___x_3897_, v___x_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3900_; uint8_t v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec_ref(v___x_3899_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136));
v___x_3901_ = 0;
v___x_3902_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__25_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_));
v___x_3903_ = l_Lean_registerTraceClass(v___x_3900_, v___x_3901_, v___x_3902_);
return v___x_3903_;
}
else
{
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2____boxed(lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_();
return v_res_3905_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm = _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm();
lean_mark_persistent(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_Deriving(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Rpc_Deriving(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Rpc_Deriving(builtin);
}
#ifdef __cplusplus
}
#endif
