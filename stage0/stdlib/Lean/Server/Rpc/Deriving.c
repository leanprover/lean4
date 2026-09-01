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
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(115, 27, 24, 243, 204, 49, 153, 202)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcEncode"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(181, 130, 28, 14, 164, 108, 68, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(147, 95, 3, 206, 143, 66, 59, 169)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcDecode"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(18, 61, 22, 59, 236, 209, 187, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(220, 0, 93, 28, 42, 216, 37, 123)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 100, 102, 194, 167, 62, 107, 182)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__79_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mapM"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(58, 78, 170, 251, 181, 31, 172, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__83 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__83_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__rpcref"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__84 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__84_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(120, 248, 178, 198, 26, 146, 90, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__85 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__85_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "'__rpcref' is reserved and cannot be used as a field name. See the `RpcEncodable` docstring."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__86 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__86_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__87;
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
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "enc"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_value),LEAN_SCALAR_PTR_LITERAL(127, 112, 184, 188, 166, 208, 172, 147)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 154, 178, 201, 214, 183, 192)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_value),LEAN_SCALAR_PTR_LITERAL(112, 200, 227, 76, 90, 242, 6, 135)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_value),LEAN_SCALAR_PTR_LITERAL(240, 112, 235, 135, 88, 35, 83, 81)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "j"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_value),LEAN_SCALAR_PTR_LITERAL(71, 110, 153, 29, 75, 133, 244, 52)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fromJson\?"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value),LEAN_SCALAR_PTR_LITERAL(3, 54, 193, 250, 66, 68, 188, 53)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value),LEAN_SCALAR_PTR_LITERAL(196, 88, 105, 59, 236, 221, 213, 61)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 131, 12, 184, 158, 202, 243, 28)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "for structure "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with params "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142;
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(79, 45, 83, 138, 97, 177, 55, 171)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rpc"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 191, 146, 242, 66, 17, 254, 170)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value),LEAN_SCALAR_PTR_LITERAL(158, 127, 243, 163, 48, 99, 68, 29)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(103, 87, 172, 78, 42, 229, 166, 12)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 39, 125, 197, 167, 200, 226, 135)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(79, 198, 180, 110, 20, 95, 155, 100)}};
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
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(201, 123, 171, 151, 210, 10, 201, 136)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 91, 41, 51, 232, 164, 71, 24)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__19_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value),LEAN_SCALAR_PTR_LITERAL(232, 134, 14, 149, 197, 132, 95, 130)}};
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
v_options_62_ = lean_ctor_get(v___y_54_, 1);
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
v_ref_85_ = lean_ctor_get(v___y_82_, 4);
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
v___x_122_ = lean_st_ref_put(v___y_83_, v___x_121_);
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
lean_dec_ref_known(v___x_238_, 1);
v___x_240_ = lean_unsigned_to_nat(0u);
v_bs_x27_241_ = lean_array_uset(v_bs_230_, v_i_229_, v___x_240_);
v___x_242_ = l_Lean_LocalDecl_userName(v_a_239_);
lean_dec(v_a_239_);
v___x_243_ = l_Lean_mkIdent(v___x_242_);
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
v_ref_274_ = lean_ctor_get(v___y_271_, 4);
v___x_275_ = l_Lean_SourceInfo_fromRef(v_ref_274_, v___x_266_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1___boxed(lean_object* v___x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
uint8_t v___x_30346__boxed_285_; lean_object* v_res_286_; 
v___x_30346__boxed_285_ = lean_unbox(v___x_277_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(v___x_30346__boxed_285_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
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
v_ref_294_ = lean_ctor_get(v___y_291_, 4);
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
lean_dec_ref_known(v___x_311_, 1);
if (lean_obj_tag(v_val_313_) == 1)
{
uint8_t v_v_314_; 
v_v_314_ = lean_ctor_get_uint8(v_val_313_, 0);
lean_dec_ref_known(v_val_313_, 0);
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
v_options_362_ = lean_ctor_get(v___y_360_, 1);
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
v_ref_398_ = lean_ctor_get(v___y_395_, 4);
v___x_399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__0(v_msg_390_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref(v___x_399_);
v_macroStack_401_ = lean_ctor_get(v___y_391_, 1);
v___x_402_ = l_Lean_Elab_getBetterRef(v_ref_398_, v_macroStack_401_);
lean_inc(v_macroStack_401_);
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
v___x_476_ = l_String_toRawSubstring_x27(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
v___x_499_ = l_String_toRawSubstring_x27(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38));
v___x_513_ = l_String_toRawSubstring_x27(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44));
v___x_529_ = l_String_toRawSubstring_x27(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1));
v___x_562_ = l_String_toRawSubstring_x27(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__81));
v___x_627_ = l_String_toRawSubstring_x27(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__87(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__86));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(lean_object* v_as_636_, size_t v_sz_637_, size_t v_i_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_a_648_; uint8_t v___x_652_; 
v___x_652_ = lean_usize_dec_lt(v_i_638_, v_sz_637_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_b_639_);
return v___x_653_;
}
else
{
lean_object* v_snd_654_; lean_object* v_snd_655_; lean_object* v_fst_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_923_; 
v_snd_654_ = lean_ctor_get(v_b_639_, 1);
lean_inc(v_snd_654_);
v_snd_655_ = lean_ctor_get(v_snd_654_, 1);
lean_inc(v_snd_655_);
v_fst_656_ = lean_ctor_get(v_b_639_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_b_639_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_b_639_, 1);
lean_dec(v_unused_924_);
v___x_658_ = v_b_639_;
v_isShared_659_ = v_isSharedCheck_923_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_fst_656_);
lean_dec(v_b_639_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_923_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_fst_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_921_; 
v_fst_660_ = lean_ctor_get(v_snd_654_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_snd_654_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_snd_654_, 1);
lean_dec(v_unused_922_);
v___x_662_ = v_snd_654_;
v_isShared_663_ = v_isSharedCheck_921_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_fst_660_);
lean_dec(v_snd_654_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_921_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_fst_664_; lean_object* v_snd_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_920_; 
v_fst_664_ = lean_ctor_get(v_snd_655_, 0);
v_snd_665_ = lean_ctor_get(v_snd_655_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_snd_655_);
if (v_isSharedCheck_920_ == 0)
{
v___x_667_ = v_snd_655_;
v_isShared_668_ = v_isSharedCheck_920_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_snd_665_);
lean_inc(v_fst_664_);
lean_dec(v_snd_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_920_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_a_669_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_a_669_ = lean_array_uget_borrowed(v_as_636_, v_i_638_);
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__85));
v___x_909_ = lean_name_eq(v_a_669_, v___x_908_);
if (v___x_909_ == 0)
{
v___y_671_ = v___y_640_;
v___y_672_ = v___y_641_;
v___y_673_ = v___y_642_;
v___y_674_ = v___y_643_;
v___y_675_ = v___y_644_;
v___y_676_ = v___y_645_;
goto v___jp_670_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__87, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__87_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__87);
v___x_911_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_910_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_dec_ref_known(v___x_911_, 1);
v___y_671_ = v___y_640_;
v___y_672_ = v___y_641_;
v___y_673_ = v___y_642_;
v___y_674_ = v___y_643_;
v___y_675_ = v___y_644_;
v___y_676_ = v___y_645_;
goto v___jp_670_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_667_);
lean_dec(v_snd_665_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
lean_dec(v_fst_656_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
v___jp_670_:
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
lean_inc_n(v_a_669_, 2);
v___x_677_ = l_Lean_mkIdent(v_a_669_);
lean_inc(v___x_677_);
v___x_678_ = lean_array_push(v_fst_656_, v___x_677_);
v___x_679_ = l_Lean_Server_RpcEncodable_isOptField(v_a_669_);
if (v___x_679_ == 0)
{
lean_object* v_toCold_680_; lean_object* v_ref_681_; lean_object* v_currMacroScope_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_toCold_680_ = lean_ctor_get(v___y_675_, 0);
v_ref_681_ = lean_ctor_get(v___y_675_, 4);
v_currMacroScope_682_ = lean_ctor_get(v___y_675_, 9);
v___x_683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(v___x_679_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_quotContext_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_n(v_a_685_, 15);
lean_dec_ref_known(v___x_684_, 1);
v_quotContext_686_ = lean_ctor_get(v_toCold_680_, 2);
v___x_687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4));
v___x_688_ = lean_box(0);
v___x_689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v_a_685_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set(v___x_693_, 2, v___x_692_);
lean_inc_ref_n(v___x_693_, 3);
lean_inc_n(v___x_677_, 2);
v___x_694_ = l_Lean_Syntax_node2(v_a_685_, v___x_690_, v___x_677_, v___x_693_);
v___x_695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_685_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_700_, 0, v_a_685_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_703_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24));
lean_inc_n(v_currMacroScope_682_, 2);
lean_inc_n(v_quotContext_686_, 2);
v___x_705_ = l_Lean_addMacroScope(v_quotContext_686_, v___x_704_, v_currMacroScope_682_);
v___x_706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
v___x_707_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_707_, 0, v_a_685_);
lean_ctor_set(v___x_707_, 1, v___x_703_);
lean_ctor_set(v___x_707_, 2, v___x_705_);
lean_ctor_set(v___x_707_, 3, v___x_706_);
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30));
v___x_709_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33));
v___x_711_ = l_Lean_addMacroScope(v_quotContext_686_, v___x_710_, v_currMacroScope_682_);
lean_inc(v___x_711_);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v_a_685_);
lean_ctor_set(v___x_712_, 1, v___x_709_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_ctor_set(v___x_712_, 3, v___x_688_);
v___x_713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v_a_685_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_Syntax_node3(v_a_685_, v___x_708_, v___x_712_, v___x_714_, v___x_677_);
v___x_716_ = l_Lean_Syntax_node1(v_a_685_, v___x_691_, v___x_715_);
v___x_717_ = l_Lean_Syntax_node2(v_a_685_, v___x_702_, v___x_707_, v___x_716_);
v___x_718_ = l_Lean_Syntax_node1(v_a_685_, v___x_701_, v___x_717_);
v___x_719_ = l_Lean_Syntax_node2(v_a_685_, v___x_698_, v___x_700_, v___x_718_);
v___x_720_ = l_Lean_Syntax_node3(v_a_685_, v___x_695_, v___x_697_, v___x_693_, v___x_719_);
v___x_721_ = l_Lean_Syntax_node3(v_a_685_, v___x_691_, v___x_693_, v___x_693_, v___x_720_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(v___x_679_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_n(v_a_723_, 15);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = l_Lean_SourceInfo_fromRef(v_ref_681_, v___x_679_);
lean_inc_n(v_currMacroScope_682_, 2);
lean_inc_n(v_quotContext_686_, 2);
v___x_725_ = l_Lean_addMacroScope(v_quotContext_686_, v___x_687_, v_currMacroScope_682_);
v___x_726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
v___x_727_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_727_, 0, v___x_724_);
lean_ctor_set(v___x_727_, 1, v___x_683_);
lean_ctor_set(v___x_727_, 2, v___x_725_);
lean_ctor_set(v___x_727_, 3, v___x_726_);
v___x_728_ = lean_array_push(v_fst_660_, v___x_727_);
v___x_729_ = l_Lean_Syntax_node2(v_a_685_, v___x_689_, v___x_694_, v___x_721_);
v___x_730_ = lean_array_push(v_fst_664_, v___x_729_);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v_a_723_);
lean_ctor_set(v___x_731_, 1, v___x_691_);
lean_ctor_set(v___x_731_, 2, v___x_692_);
lean_inc_ref_n(v___x_731_, 3);
lean_inc(v___x_677_);
v___x_732_ = l_Lean_Syntax_node2(v_a_723_, v___x_690_, v___x_677_, v___x_731_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_723_);
lean_ctor_set(v___x_733_, 1, v___x_696_);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v_a_723_);
lean_ctor_set(v___x_734_, 1, v___x_699_);
v___x_735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39);
v___x_736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
v___x_737_ = l_Lean_addMacroScope(v_quotContext_686_, v___x_736_, v_currMacroScope_682_);
v___x_738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43));
v___x_739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_739_, 0, v_a_723_);
lean_ctor_set(v___x_739_, 1, v___x_735_);
lean_ctor_set(v___x_739_, 2, v___x_737_);
lean_ctor_set(v___x_739_, 3, v___x_738_);
v___x_740_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_740_, 0, v_a_723_);
lean_ctor_set(v___x_740_, 1, v___x_709_);
lean_ctor_set(v___x_740_, 2, v___x_711_);
lean_ctor_set(v___x_740_, 3, v___x_688_);
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_723_);
lean_ctor_set(v___x_741_, 1, v___x_713_);
v___x_742_ = l_Lean_Syntax_node3(v_a_723_, v___x_708_, v___x_740_, v___x_741_, v___x_677_);
v___x_743_ = l_Lean_Syntax_node1(v_a_723_, v___x_691_, v___x_742_);
v___x_744_ = l_Lean_Syntax_node2(v_a_723_, v___x_702_, v___x_739_, v___x_743_);
v___x_745_ = l_Lean_Syntax_node1(v_a_723_, v___x_701_, v___x_744_);
v___x_746_ = l_Lean_Syntax_node2(v_a_723_, v___x_698_, v___x_734_, v___x_745_);
v___x_747_ = l_Lean_Syntax_node3(v_a_723_, v___x_695_, v___x_733_, v___x_731_, v___x_746_);
v___x_748_ = l_Lean_Syntax_node3(v_a_723_, v___x_691_, v___x_731_, v___x_731_, v___x_747_);
v___x_749_ = l_Lean_Syntax_node2(v_a_723_, v___x_689_, v___x_732_, v___x_748_);
v___x_750_ = lean_array_push(v_snd_665_, v___x_749_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_750_);
lean_ctor_set(v___x_667_, 0, v___x_730_);
v___x_752_ = v___x_667_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_759_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_752_);
lean_ctor_set(v___x_662_, 0, v___x_728_);
v___x_754_ = v___x_662_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_754_);
lean_ctor_set(v___x_658_, 0, v___x_678_);
v___x_756_ = v___x_658_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v_a_648_ = v___x_756_;
goto v___jp_647_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v___x_721_);
lean_dec(v___x_711_);
lean_dec(v___x_694_);
lean_dec(v_a_685_);
lean_dec_ref(v___x_678_);
lean_dec(v___x_677_);
lean_del_object(v___x_667_);
lean_dec(v_snd_665_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
v_a_760_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_722_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_722_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v___x_678_);
lean_dec(v___x_677_);
lean_del_object(v___x_667_);
lean_dec(v_snd_665_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
v_a_768_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_684_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_684_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_toCold_776_; lean_object* v_ref_777_; lean_object* v_currMacroScope_778_; lean_object* v_quotContext_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_toCold_776_ = lean_ctor_get(v___y_675_, 0);
v_ref_777_ = lean_ctor_get(v___y_675_, 4);
v_currMacroScope_778_ = lean_ctor_get(v___y_675_, 9);
v_quotContext_779_ = lean_ctor_get(v_toCold_776_, 2);
v___x_780_ = 0;
v___x_781_ = l_Lean_SourceInfo_fromRef(v_ref_777_, v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46));
lean_inc(v_currMacroScope_778_);
lean_inc(v_quotContext_779_);
v___x_785_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_784_, v_currMacroScope_778_);
v___x_786_ = lean_box(0);
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
lean_inc(v___x_781_);
v___x_788_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_788_, 0, v___x_781_);
lean_ctor_set(v___x_788_, 1, v___x_783_);
lean_ctor_set(v___x_788_, 2, v___x_785_);
lean_ctor_set(v___x_788_, 3, v___x_787_);
v___x_789_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3);
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4));
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_n(v_a_792_, 23);
lean_dec_ref_known(v___x_791_, 1);
lean_inc_n(v_currMacroScope_778_, 5);
lean_inc_n(v_quotContext_779_, 5);
v___x_793_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_790_, v_currMacroScope_778_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc_n(v___x_781_, 2);
v___x_795_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_795_, 0, v___x_781_);
lean_ctor_set(v___x_795_, 1, v___x_789_);
lean_ctor_set(v___x_795_, 2, v___x_793_);
lean_ctor_set(v___x_795_, 3, v___x_794_);
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_797_ = l_Lean_Syntax_node1(v___x_781_, v___x_796_, v___x_795_);
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v_a_792_);
lean_ctor_set(v___x_801_, 1, v___x_796_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
lean_inc_ref_n(v___x_801_, 3);
lean_inc_n(v___x_677_, 2);
v___x_802_ = l_Lean_Syntax_node2(v_a_792_, v___x_799_, v___x_677_, v___x_801_);
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v_a_792_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_792_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30));
v___x_811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
v___x_812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_792_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57));
v___x_816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58);
v___x_817_ = lean_box(0);
v___x_818_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_817_, v_currMacroScope_778_);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__80));
lean_inc(v___x_818_);
v___x_820_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_820_, 0, v_a_792_);
lean_ctor_set(v___x_820_, 1, v___x_816_);
lean_ctor_set(v___x_820_, 2, v___x_818_);
lean_ctor_set(v___x_820_, 3, v___x_819_);
v___x_821_ = l_Lean_Syntax_node1(v_a_792_, v___x_815_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node2(v_a_792_, v___x_812_, v___x_814_, v___x_821_);
v___x_823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33));
v___x_825_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_824_, v_currMacroScope_778_);
lean_inc(v___x_825_);
v___x_826_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_826_, 0, v_a_792_);
lean_ctor_set(v___x_826_, 1, v___x_823_);
lean_ctor_set(v___x_826_, 2, v___x_825_);
lean_ctor_set(v___x_826_, 3, v___x_786_);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34));
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v_a_792_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
lean_inc_ref(v___x_828_);
v___x_829_ = l_Lean_Syntax_node3(v_a_792_, v___x_810_, v___x_826_, v___x_828_, v___x_677_);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_831_, 0, v_a_792_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_Syntax_node3(v_a_792_, v___x_811_, v___x_822_, v___x_829_, v___x_831_);
v___x_833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__82);
v___x_834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__83));
v___x_835_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_834_, v_currMacroScope_778_);
lean_inc(v___x_835_);
v___x_836_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_836_, 0, v_a_792_);
lean_ctor_set(v___x_836_, 1, v___x_833_);
lean_ctor_set(v___x_836_, 2, v___x_835_);
lean_ctor_set(v___x_836_, 3, v___x_786_);
v___x_837_ = l_Lean_Syntax_node3(v_a_792_, v___x_810_, v___x_832_, v___x_828_, v___x_836_);
v___x_838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24));
v___x_840_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_839_, v_currMacroScope_778_);
v___x_841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
v___x_842_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_842_, 0, v_a_792_);
lean_ctor_set(v___x_842_, 1, v___x_838_);
lean_ctor_set(v___x_842_, 2, v___x_840_);
lean_ctor_set(v___x_842_, 3, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v_a_792_, v___x_796_, v___x_842_);
v___x_844_ = l_Lean_Syntax_node2(v_a_792_, v___x_782_, v___x_837_, v___x_843_);
v___x_845_ = l_Lean_Syntax_node1(v_a_792_, v___x_809_, v___x_844_);
v___x_846_ = l_Lean_Syntax_node2(v_a_792_, v___x_806_, v___x_808_, v___x_845_);
v___x_847_ = l_Lean_Syntax_node3(v_a_792_, v___x_803_, v___x_805_, v___x_801_, v___x_846_);
v___x_848_ = l_Lean_Syntax_node3(v_a_792_, v___x_796_, v___x_801_, v___x_801_, v___x_847_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_n(v_a_850_, 23);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = l_Lean_Syntax_node2(v___x_781_, v___x_782_, v___x_788_, v___x_797_);
v___x_852_ = lean_array_push(v_fst_660_, v___x_851_);
v___x_853_ = l_Lean_Syntax_node2(v_a_792_, v___x_798_, v___x_802_, v___x_848_);
v___x_854_ = lean_array_push(v_fst_664_, v___x_853_);
v___x_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_855_, 0, v_a_850_);
lean_ctor_set(v___x_855_, 1, v___x_796_);
lean_ctor_set(v___x_855_, 2, v___x_800_);
lean_inc_ref_n(v___x_855_, 3);
lean_inc(v___x_677_);
v___x_856_ = l_Lean_Syntax_node2(v_a_850_, v___x_799_, v___x_677_, v___x_855_);
v___x_857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_857_, 0, v_a_850_);
lean_ctor_set(v___x_857_, 1, v___x_804_);
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v_a_850_);
lean_ctor_set(v___x_858_, 1, v___x_807_);
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v_a_850_);
lean_ctor_set(v___x_859_, 1, v___x_813_);
v___x_860_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_860_, 0, v_a_850_);
lean_ctor_set(v___x_860_, 1, v___x_816_);
lean_ctor_set(v___x_860_, 2, v___x_818_);
lean_ctor_set(v___x_860_, 3, v___x_819_);
v___x_861_ = l_Lean_Syntax_node1(v_a_850_, v___x_815_, v___x_860_);
v___x_862_ = l_Lean_Syntax_node2(v_a_850_, v___x_812_, v___x_859_, v___x_861_);
v___x_863_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_863_, 0, v_a_850_);
lean_ctor_set(v___x_863_, 1, v___x_823_);
lean_ctor_set(v___x_863_, 2, v___x_825_);
lean_ctor_set(v___x_863_, 3, v___x_786_);
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v_a_850_);
lean_ctor_set(v___x_864_, 1, v___x_827_);
lean_inc_ref(v___x_864_);
v___x_865_ = l_Lean_Syntax_node3(v_a_850_, v___x_810_, v___x_863_, v___x_864_, v___x_677_);
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v_a_850_);
lean_ctor_set(v___x_866_, 1, v___x_830_);
v___x_867_ = l_Lean_Syntax_node3(v_a_850_, v___x_811_, v___x_862_, v___x_865_, v___x_866_);
v___x_868_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_868_, 0, v_a_850_);
lean_ctor_set(v___x_868_, 1, v___x_833_);
lean_ctor_set(v___x_868_, 2, v___x_835_);
lean_ctor_set(v___x_868_, 3, v___x_786_);
v___x_869_ = l_Lean_Syntax_node3(v_a_850_, v___x_810_, v___x_867_, v___x_864_, v___x_868_);
v___x_870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39);
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(v_currMacroScope_778_);
lean_inc(v_quotContext_779_);
v___x_872_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_871_, v_currMacroScope_778_);
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43));
v___x_874_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_874_, 0, v_a_850_);
lean_ctor_set(v___x_874_, 1, v___x_870_);
lean_ctor_set(v___x_874_, 2, v___x_872_);
lean_ctor_set(v___x_874_, 3, v___x_873_);
v___x_875_ = l_Lean_Syntax_node1(v_a_850_, v___x_796_, v___x_874_);
v___x_876_ = l_Lean_Syntax_node2(v_a_850_, v___x_782_, v___x_869_, v___x_875_);
v___x_877_ = l_Lean_Syntax_node1(v_a_850_, v___x_809_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node2(v_a_850_, v___x_806_, v___x_858_, v___x_877_);
v___x_879_ = l_Lean_Syntax_node3(v_a_850_, v___x_803_, v___x_857_, v___x_855_, v___x_878_);
v___x_880_ = l_Lean_Syntax_node3(v_a_850_, v___x_796_, v___x_855_, v___x_855_, v___x_879_);
v___x_881_ = l_Lean_Syntax_node2(v_a_850_, v___x_798_, v___x_856_, v___x_880_);
v___x_882_ = lean_array_push(v_snd_665_, v___x_881_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_882_);
lean_ctor_set(v___x_667_, 0, v___x_854_);
v___x_884_ = v___x_667_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_891_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_884_);
lean_ctor_set(v___x_662_, 0, v___x_852_);
v___x_886_ = v___x_662_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_886_);
lean_ctor_set(v___x_658_, 0, v___x_678_);
v___x_888_ = v___x_658_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_a_648_ = v___x_888_;
goto v___jp_647_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v___x_848_);
lean_dec(v___x_835_);
lean_dec(v___x_825_);
lean_dec(v___x_818_);
lean_dec(v___x_802_);
lean_dec(v___x_797_);
lean_dec(v_a_792_);
lean_dec_ref_known(v___x_788_, 4);
lean_dec(v___x_781_);
lean_dec_ref(v___x_678_);
lean_dec(v___x_677_);
lean_del_object(v___x_667_);
lean_dec(v_snd_665_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
v_a_892_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_849_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_849_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref_known(v___x_788_, 4);
lean_dec(v___x_781_);
lean_dec_ref(v___x_678_);
lean_dec(v___x_677_);
lean_del_object(v___x_667_);
lean_dec(v_snd_665_);
lean_dec(v_fst_664_);
lean_del_object(v___x_662_);
lean_dec(v_fst_660_);
lean_del_object(v___x_658_);
v_a_900_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_791_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_791_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
}
}
v___jp_647_:
{
size_t v___x_649_; size_t v___x_650_; 
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_638_, v___x_649_);
v_i_638_ = v___x_650_;
v_b_639_ = v_a_648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___boxed(lean_object* v_as_925_, lean_object* v_sz_926_, lean_object* v_i_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
size_t v_sz_boxed_936_; size_t v_i_boxed_937_; lean_object* v_res_938_; 
v_sz_boxed_936_ = lean_unbox_usize(v_sz_926_);
lean_dec(v_sz_926_);
v_i_boxed_937_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(v_as_925_, v_sz_boxed_936_, v_i_boxed_937_, v_b_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_as_925_);
return v_res_938_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14));
v___x_981_ = l_String_toRawSubstring_x27(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25));
v___x_1006_ = l_String_toRawSubstring_x27(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34));
v___x_1026_ = l_String_toRawSubstring_x27(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0));
v___x_1074_ = l_String_toRawSubstring_x27(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76));
v___x_1141_ = l_String_toRawSubstring_x27(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81));
v___x_1152_ = l_String_toRawSubstring_x27(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103));
v___x_1208_ = l_String_toRawSubstring_x27(v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33));
v___x_1222_ = l_Lean_mkAtom(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110));
v___x_1225_ = l_String_toRawSubstring_x27(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126));
v___x_1267_ = l_String_toRawSubstring_x27(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135));
v___x_1295_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137));
v___x_1296_ = l_Lean_Name_append(v___x_1295_, v___x_1294_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__139));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__141));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(lean_object* v_indVal_1303_, lean_object* v_params_1304_, lean_object* v_encInstBinders_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v_toConstantVal_1314_; lean_object* v_options_1315_; lean_object* v_env_1316_; lean_object* v_name_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1660_; 
v___x_1313_ = lean_st_ref_get(v_a_1311_);
v_toConstantVal_1314_ = lean_ctor_get(v_indVal_1303_, 0);
lean_inc_ref(v_toConstantVal_1314_);
lean_dec_ref(v_indVal_1303_);
v_options_1315_ = lean_ctor_get(v_a_1310_, 1);
v_env_1316_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_ref(v_env_1316_);
lean_dec(v___x_1313_);
v_name_1317_ = lean_ctor_get(v_toConstantVal_1314_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_toConstantVal_1314_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; 
v_unused_1661_ = lean_ctor_get(v_toConstantVal_1314_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_toConstantVal_1314_, 1);
lean_dec(v_unused_1662_);
v___x_1319_ = v_toConstantVal_1314_;
v_isShared_1320_ = v_isSharedCheck_1660_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_name_1317_);
lean_dec(v_toConstantVal_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1660_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_toCold_1321_; uint8_t v_hasTrace_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; 
v_toCold_1321_ = lean_ctor_get(v_a_1310_, 0);
v_hasTrace_1322_ = lean_ctor_get_uint8(v_options_1315_, sizeof(void*)*1);
v___x_1323_ = 0;
lean_inc(v_name_1317_);
v___x_1324_ = l_Lean_getStructureFieldsFlattened(v_env_1316_, v_name_1317_, v___x_1323_);
if (v_hasTrace_1322_ == 0)
{
v___y_1326_ = v_a_1306_;
v___y_1327_ = v_a_1307_;
v___y_1328_ = v_a_1308_;
v___y_1329_ = v_a_1309_;
v___y_1330_ = v_a_1310_;
v___y_1331_ = v_a_1311_;
goto v___jp_1325_;
}
else
{
lean_object* v_inheritedTraceOptions_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_inheritedTraceOptions_1637_ = lean_ctor_get(v_toCold_1321_, 4);
v___x_1638_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135));
v___x_1639_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138);
v___x_1640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1637_, v_options_1315_, v___x_1639_);
if (v___x_1640_ == 0)
{
v___y_1326_ = v_a_1306_;
v___y_1327_ = v_a_1307_;
v___y_1328_ = v_a_1308_;
v___y_1329_ = v_a_1309_;
v___y_1330_ = v_a_1310_;
v___y_1331_ = v_a_1311_;
goto v___jp_1325_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1641_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__140);
lean_inc(v_name_1317_);
v___x_1642_ = l_Lean_MessageData_ofName(v_name_1317_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
lean_inc_ref(v_params_1304_);
v___x_1646_ = lean_array_to_list(v_params_1304_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(v___x_1646_, v___x_1647_);
v___x_1649_ = l_Lean_MessageData_ofList(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1645_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v___x_1638_, v___x_1650_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_dec_ref_known(v___x_1651_, 1);
v___y_1326_ = v_a_1306_;
v___y_1327_ = v_a_1307_;
v___y_1328_ = v_a_1308_;
v___y_1329_ = v_a_1309_;
v___y_1330_ = v_a_1310_;
v___y_1331_ = v_a_1311_;
goto v___jp_1325_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___x_1324_);
lean_del_object(v___x_1319_);
lean_dec(v_name_1317_);
lean_dec_ref(v_params_1304_);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
v___jp_1325_:
{
lean_object* v___x_1332_; size_t v_sz_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3));
v_sz_1333_ = lean_array_size(v___x_1324_);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(v___x_1324_, v_sz_1333_, v___x_1334_, v___x_1332_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec_ref(v___x_1324_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; size_t v_sz_1337_; lean_object* v___x_1338_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v_sz_1337_ = lean_array_size(v_params_1304_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_1337_, v___x_1334_, v_params_1304_, v___y_1328_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_snd_1339_; lean_object* v_snd_1340_; lean_object* v_toCold_1341_; lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1620_; 
v_snd_1339_ = lean_ctor_get(v_a_1336_, 1);
lean_inc(v_snd_1339_);
v_snd_1340_ = lean_ctor_get(v_snd_1339_, 1);
lean_inc(v_snd_1340_);
v_toCold_1341_ = lean_ctor_get(v___y_1330_, 0);
v_a_1342_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1344_ = v___x_1338_;
v_isShared_1345_ = v_isSharedCheck_1620_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1338_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1620_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_fst_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1618_; 
v_fst_1346_ = lean_ctor_get(v_a_1336_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_a_1336_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_a_1336_, 1);
lean_dec(v_unused_1619_);
v___x_1348_ = v_a_1336_;
v_isShared_1349_ = v_isSharedCheck_1618_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_fst_1346_);
lean_dec(v_a_1336_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1618_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_fst_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1616_; 
v_fst_1350_ = lean_ctor_get(v_snd_1339_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_snd_1339_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v_snd_1339_, 1);
lean_dec(v_unused_1617_);
v___x_1352_ = v_snd_1339_;
v_isShared_1353_ = v_isSharedCheck_1616_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_fst_1350_);
lean_dec(v_snd_1339_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1616_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1615_; 
v_fst_1354_ = lean_ctor_get(v_snd_1340_, 0);
v_snd_1355_ = lean_ctor_get(v_snd_1340_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_snd_1340_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1357_ = v_snd_1340_;
v_isShared_1358_ = v_isSharedCheck_1615_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v_snd_1340_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1615_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_ref_1359_; lean_object* v_currMacroScope_1360_; lean_object* v_quotContext_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v_ref_1359_ = lean_ctor_get(v___y_1330_, 4);
v_currMacroScope_1360_ = lean_ctor_get(v___y_1330_, 9);
v_quotContext_1361_ = lean_ctor_get(v_toCold_1341_, 2);
v___x_1362_ = l_Lean_SourceInfo_fromRef(v_ref_1359_, v___x_1323_);
v___x_1363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_1364_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5));
v___x_1365_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
v___x_1366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
lean_inc(v___x_1362_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 1);
lean_ctor_set(v___x_1319_, 2, v___x_1366_);
lean_ctor_set(v___x_1319_, 1, v___x_1363_);
lean_ctor_set(v___x_1319_, 0, v___x_1362_);
v___x_1368_ = v___x_1319_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc_ref_n(v___x_1368_, 7);
lean_inc_n(v___x_1362_, 2);
v___x_1369_ = l_Lean_Syntax_node7(v___x_1362_, v___x_1365_, v___x_1368_, v___x_1368_, v___x_1368_, v___x_1368_, v___x_1368_, v___x_1368_, v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8));
v___x_1371_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9));
v___x_1372_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11));
if (v_isShared_1358_ == 0)
{
lean_ctor_set_tag(v___x_1357_, 2);
lean_ctor_set(v___x_1357_, 1, v___x_1370_);
lean_ctor_set(v___x_1357_, 0, v___x_1362_);
v___x_1374_ = v___x_1357_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1370_);
v___x_1374_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_inc_n(v___x_1362_, 5);
v___x_1375_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1372_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13));
v___x_1377_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15);
v___x_1378_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
lean_inc(v_currMacroScope_1360_);
lean_inc(v_quotContext_1361_);
v___x_1379_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1378_, v_currMacroScope_1360_);
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1362_);
lean_ctor_set(v___x_1381_, 1, v___x_1377_);
lean_ctor_set(v___x_1381_, 2, v___x_1379_);
lean_ctor_set(v___x_1381_, 3, v___x_1380_);
lean_inc_ref_n(v___x_1368_, 3);
lean_inc_ref(v___x_1381_);
v___x_1382_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1376_, v___x_1381_, v___x_1368_);
v___x_1383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_1384_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1383_, v___x_1368_, v___x_1368_);
v___x_1385_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17));
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 2);
lean_ctor_set(v___x_1352_, 1, v___x_1385_);
lean_ctor_set(v___x_1352_, 0, v___x_1362_);
v___x_1387_ = v___x_1352_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; size_t v_sz_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1388_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19));
v___x_1389_ = l_Array_zip___redArg(v_fst_1346_, v_fst_1350_);
lean_dec(v_fst_1350_);
lean_dec(v_fst_1346_);
v_sz_1390_ = lean_array_size(v___x_1389_);
lean_inc(v___x_1369_);
lean_inc_ref_n(v___x_1368_, 2);
lean_inc_n(v___x_1362_, 5);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(v___x_1362_, v___x_1368_, v___x_1369_, v_sz_1390_, v___x_1334_, v___x_1389_);
v___x_1392_ = l_Array_append___redArg(v___x_1366_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1362_);
lean_ctor_set(v___x_1393_, 1, v___x_1363_);
lean_ctor_set(v___x_1393_, 2, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1388_, v___x_1393_);
lean_inc_ref(v___x_1387_);
v___x_1395_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1363_, v___x_1387_, v___x_1368_, v___x_1394_);
v___x_1396_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21));
v___x_1397_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22));
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 2);
lean_ctor_set(v___x_1348_, 1, v___x_1397_);
lean_ctor_set(v___x_1348_, 0, v___x_1362_);
v___x_1399_ = v___x_1348_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; size_t v_sz_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; size_t v_sz_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24));
v___x_1401_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26);
v___x_1402_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27));
lean_inc_n(v_currMacroScope_1360_, 12);
lean_inc_n(v_quotContext_1361_, 12);
v___x_1403_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1402_, v_currMacroScope_1360_);
v___x_1404_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32));
lean_inc_n(v___x_1362_, 102);
v___x_1405_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1362_);
lean_ctor_set(v___x_1405_, 1, v___x_1401_);
lean_ctor_set(v___x_1405_, 2, v___x_1403_);
lean_ctor_set(v___x_1405_, 3, v___x_1404_);
lean_inc_ref_n(v___x_1368_, 34);
v___x_1406_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1400_, v___x_1368_, v___x_1405_);
v___x_1407_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33));
v___x_1408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1362_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35);
v___x_1410_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36));
v___x_1411_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1410_, v_currMacroScope_1360_);
v___x_1412_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41));
v___x_1413_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1362_);
lean_ctor_set(v___x_1413_, 1, v___x_1409_);
lean_ctor_set(v___x_1413_, 2, v___x_1411_);
lean_ctor_set(v___x_1413_, 3, v___x_1412_);
v___x_1414_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1400_, v___x_1368_, v___x_1413_);
lean_inc_ref(v___x_1408_);
v___x_1415_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1363_, v___x_1406_, v___x_1408_, v___x_1414_);
v___x_1416_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1363_, v___x_1399_, v___x_1415_);
v___x_1417_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1396_, v___x_1416_);
v___x_1418_ = l_Lean_Syntax_node6(v___x_1362_, v___x_1371_, v___x_1375_, v___x_1382_, v___x_1384_, v___x_1368_, v___x_1395_, v___x_1417_);
lean_inc(v___x_1369_);
v___x_1419_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1364_, v___x_1369_, v___x_1418_);
v___x_1420_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42));
v___x_1421_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43));
v___x_1422_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44));
v___x_1423_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45));
v___x_1424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1362_);
lean_ctor_set(v___x_1424_, 1, v___x_1422_);
v___x_1425_ = l_Array_append___redArg(v___x_1366_, v_encInstBinders_1305_);
v___x_1426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1362_);
lean_ctor_set(v___x_1426_, 1, v___x_1363_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
v___x_1427_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1423_, v___x_1424_, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1362_);
lean_ctor_set(v___x_1428_, 1, v___x_1420_);
v___x_1429_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46));
v___x_1430_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47));
v___x_1431_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49));
v___x_1432_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1431_, v___x_1368_);
v___x_1433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1362_);
lean_ctor_set(v___x_1433_, 1, v___x_1429_);
v___x_1434_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51));
v___x_1435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_1436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_1437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1362_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_1439_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52);
v___x_1440_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
v___x_1441_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1440_, v_currMacroScope_1360_);
v___x_1442_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56));
v___x_1443_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1362_);
lean_ctor_set(v___x_1443_, 1, v___x_1439_);
lean_ctor_set(v___x_1443_, 2, v___x_1441_);
lean_ctor_set(v___x_1443_, 3, v___x_1442_);
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
v___x_1445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
v___x_1446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
v___x_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1362_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57));
v___x_1449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58);
v___x_1450_ = lean_box(0);
v___x_1451_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1450_, v_currMacroScope_1360_);
v___x_1452_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63));
v___x_1453_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1362_);
lean_ctor_set(v___x_1453_, 1, v___x_1449_);
lean_ctor_set(v___x_1453_, 2, v___x_1451_);
lean_ctor_set(v___x_1453_, 3, v___x_1452_);
v___x_1454_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1448_, v___x_1453_);
v___x_1455_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1445_, v___x_1447_, v___x_1454_);
v___x_1456_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65));
v___x_1457_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66));
v___x_1458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1362_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_mkCIdent(v_name_1317_);
v___x_1460_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1456_, v___x_1458_, v___x_1459_);
v_sz_1461_ = lean_array_size(v_a_1342_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(v_sz_1461_, v___x_1334_, v_a_1342_);
v___x_1463_ = l_Array_append___redArg(v___x_1366_, v___x_1462_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1362_);
lean_ctor_set(v___x_1464_, 1, v___x_1363_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1438_, v___x_1460_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1362_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1444_, v___x_1455_, v___x_1465_, v___x_1467_);
v___x_1469_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1468_);
v___x_1470_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1438_, v___x_1443_, v___x_1469_);
lean_inc_ref_n(v___x_1437_, 2);
v___x_1471_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1435_, v___x_1437_, v___x_1470_);
v___x_1472_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1434_, v___x_1368_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68));
v___x_1474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_1475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1362_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70));
v___x_1477_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71));
v___x_1478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1362_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73));
v___x_1480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_1482_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23);
v___x_1483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24));
v___x_1484_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1483_, v_currMacroScope_1360_);
v___x_1485_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75));
v___x_1486_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1362_);
lean_ctor_set(v___x_1486_, 1, v___x_1482_);
lean_ctor_set(v___x_1486_, 2, v___x_1484_);
lean_ctor_set(v___x_1486_, 3, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1481_, v___x_1486_, v___x_1368_);
v___x_1488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_1489_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77);
v___x_1490_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78));
v___x_1491_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1490_, v_currMacroScope_1360_);
v___x_1492_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1362_);
lean_ctor_set(v___x_1492_, 1, v___x_1489_);
lean_ctor_set(v___x_1492_, 2, v___x_1491_);
lean_ctor_set(v___x_1492_, 3, v___x_1380_);
lean_inc_ref(v___x_1492_);
lean_inc_ref_n(v___x_1475_, 4);
v___x_1493_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1488_, v___x_1475_, v___x_1368_, v___x_1492_);
v___x_1494_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1363_, v___x_1368_, v___x_1368_, v___x_1493_);
v___x_1495_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1480_, v___x_1487_, v___x_1494_);
v___x_1496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39);
v___x_1497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
v___x_1498_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1497_, v_currMacroScope_1360_);
v___x_1499_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80));
v___x_1500_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1362_);
lean_ctor_set(v___x_1500_, 1, v___x_1496_);
lean_ctor_set(v___x_1500_, 2, v___x_1498_);
lean_ctor_set(v___x_1500_, 3, v___x_1499_);
v___x_1501_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1481_, v___x_1500_, v___x_1368_);
v___x_1502_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82);
v___x_1503_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83));
v___x_1504_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1503_, v_currMacroScope_1360_);
v___x_1505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1362_);
lean_ctor_set(v___x_1505_, 1, v___x_1502_);
lean_ctor_set(v___x_1505_, 2, v___x_1504_);
lean_ctor_set(v___x_1505_, 3, v___x_1380_);
lean_inc_ref(v___x_1505_);
v___x_1506_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1488_, v___x_1475_, v___x_1368_, v___x_1505_);
v___x_1507_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1363_, v___x_1368_, v___x_1368_, v___x_1506_);
v___x_1508_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1480_, v___x_1501_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1363_, v___x_1495_, v___x_1408_, v___x_1508_);
v___x_1510_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1479_, v___x_1509_);
v___x_1511_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85));
v___x_1512_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1511_, v___x_1368_);
v___x_1513_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86));
v___x_1514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1362_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_inc_ref_n(v___x_1514_, 2);
lean_inc_n(v___x_1512_, 2);
lean_inc_ref_n(v___x_1478_, 2);
v___x_1515_ = l_Lean_Syntax_node6(v___x_1362_, v___x_1476_, v___x_1478_, v___x_1368_, v___x_1510_, v___x_1512_, v___x_1368_, v___x_1514_);
v___x_1516_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89));
v___x_1517_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1516_, v___x_1368_, v___x_1368_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91));
v___x_1519_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93));
v___x_1520_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95));
v___x_1521_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97));
v___x_1522_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99));
v___x_1523_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1522_, v___x_1492_);
v___x_1524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32);
v___x_1525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33));
v___x_1526_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1525_, v_currMacroScope_1360_);
v___x_1527_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1362_);
lean_ctor_set(v___x_1527_, 1, v___x_1524_);
lean_ctor_set(v___x_1527_, 2, v___x_1526_);
lean_ctor_set(v___x_1527_, 3, v___x_1380_);
lean_inc_ref(v___x_1527_);
v___x_1528_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1527_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101));
v___x_1530_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102));
v___x_1531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1362_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104);
v___x_1533_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105));
v___x_1534_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1533_, v_currMacroScope_1360_);
v___x_1535_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108));
v___x_1536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1362_);
lean_ctor_set(v___x_1536_, 1, v___x_1532_);
lean_ctor_set(v___x_1536_, 2, v___x_1534_);
lean_ctor_set(v___x_1536_, 3, v___x_1535_);
v_sz_1537_ = lean_array_size(v_fst_1354_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_1537_, v___x_1334_, v_fst_1354_);
v___x_1539_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109);
v___x_1540_ = l_Lean_mkSepArray(v___x_1538_, v___x_1539_);
lean_dec_ref(v___x_1538_);
v___x_1541_ = l_Array_append___redArg(v___x_1366_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1362_);
lean_ctor_set(v___x_1542_, 1, v___x_1363_);
lean_ctor_set(v___x_1542_, 2, v___x_1541_);
v___x_1543_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1479_, v___x_1542_);
lean_inc_ref(v___x_1381_);
v___x_1544_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1363_, v___x_1437_, v___x_1381_);
v___x_1545_ = l_Lean_Syntax_node6(v___x_1362_, v___x_1476_, v___x_1478_, v___x_1368_, v___x_1543_, v___x_1512_, v___x_1544_, v___x_1514_);
v___x_1546_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1545_);
v___x_1547_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1438_, v___x_1536_, v___x_1546_);
v___x_1548_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1547_);
lean_inc_ref(v___x_1531_);
v___x_1549_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1529_, v___x_1531_, v___x_1548_);
v___x_1550_ = l_Lean_Syntax_node5(v___x_1362_, v___x_1521_, v___x_1523_, v___x_1528_, v___x_1368_, v___x_1475_, v___x_1549_);
v___x_1551_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1520_, v___x_1550_);
lean_inc_n(v___x_1517_, 2);
v___x_1552_ = l_Lean_Syntax_node4(v___x_1362_, v___x_1519_, v___x_1368_, v___x_1368_, v___x_1551_, v___x_1517_);
v___x_1553_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1522_, v___x_1505_);
v___x_1554_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111);
v___x_1555_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112));
v___x_1556_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1555_, v_currMacroScope_1360_);
v___x_1557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1362_);
lean_ctor_set(v___x_1557_, 1, v___x_1554_);
lean_ctor_set(v___x_1557_, 2, v___x_1556_);
lean_ctor_set(v___x_1557_, 3, v___x_1380_);
v___x_1558_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113));
v___x_1560_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114));
v___x_1561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1362_);
lean_ctor_set(v___x_1561_, 1, v___x_1559_);
v___x_1562_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116));
v___x_1563_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118));
v___x_1564_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120));
v___x_1565_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121));
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1362_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123));
v___x_1568_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1567_, v___x_1368_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125));
v___x_1570_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1435_, v___x_1437_, v___x_1381_);
v___x_1571_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1570_);
v___x_1572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_1573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1362_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_1575_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127);
v___x_1576_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128));
v___x_1577_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1576_, v_currMacroScope_1360_);
v___x_1578_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131));
v___x_1579_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1362_);
lean_ctor_set(v___x_1579_, 1, v___x_1575_);
lean_ctor_set(v___x_1579_, 2, v___x_1577_);
lean_ctor_set(v___x_1579_, 3, v___x_1578_);
lean_inc(v___x_1558_);
v___x_1580_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1438_, v___x_1579_, v___x_1558_);
v___x_1581_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1574_, v___x_1580_);
v___x_1582_ = l_Lean_Syntax_node4(v___x_1362_, v___x_1569_, v___x_1527_, v___x_1571_, v___x_1573_, v___x_1581_);
v___x_1583_ = l_Lean_Syntax_node4(v___x_1362_, v___x_1564_, v___x_1566_, v___x_1368_, v___x_1568_, v___x_1582_);
v___x_1584_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1563_, v___x_1583_, v___x_1368_);
v___x_1585_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133));
v___x_1586_ = l_Lean_Syntax_SepArray_ofElems(v___x_1407_, v_snd_1355_);
lean_dec(v_snd_1355_);
v___x_1587_ = l_Array_append___redArg(v___x_1366_, v___x_1586_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1362_);
lean_ctor_set(v___x_1588_, 1, v___x_1363_);
lean_ctor_set(v___x_1588_, 2, v___x_1587_);
v___x_1589_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1479_, v___x_1588_);
v___x_1590_ = l_Lean_Syntax_node6(v___x_1362_, v___x_1476_, v___x_1478_, v___x_1368_, v___x_1589_, v___x_1512_, v___x_1368_, v___x_1514_);
v___x_1591_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1590_);
v___x_1592_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1585_, v___x_1531_, v___x_1591_);
v___x_1593_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1563_, v___x_1592_, v___x_1368_);
v___x_1594_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1363_, v___x_1584_, v___x_1593_);
v___x_1595_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1562_, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1560_, v___x_1561_, v___x_1595_);
v___x_1597_ = l_Lean_Syntax_node5(v___x_1362_, v___x_1521_, v___x_1553_, v___x_1558_, v___x_1368_, v___x_1475_, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1520_, v___x_1597_);
v___x_1599_ = l_Lean_Syntax_node4(v___x_1362_, v___x_1519_, v___x_1368_, v___x_1368_, v___x_1598_, v___x_1517_);
v___x_1600_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1363_, v___x_1552_, v___x_1368_, v___x_1599_);
v___x_1601_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1518_, v___x_1387_, v___x_1600_, v___x_1368_);
v___x_1602_ = l_Lean_Syntax_node1(v___x_1362_, v___x_1363_, v___x_1601_);
v___x_1603_ = l_Lean_Syntax_node4(v___x_1362_, v___x_1473_, v___x_1475_, v___x_1515_, v___x_1517_, v___x_1602_);
v___x_1604_ = l_Lean_Syntax_node6(v___x_1362_, v___x_1430_, v___x_1432_, v___x_1433_, v___x_1368_, v___x_1368_, v___x_1472_, v___x_1603_);
v___x_1605_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1364_, v___x_1369_, v___x_1604_);
v___x_1606_ = l_Lean_Syntax_node3(v___x_1362_, v___x_1421_, v___x_1427_, v___x_1428_, v___x_1605_);
v___x_1607_ = l_Lean_Syntax_node2(v___x_1362_, v___x_1363_, v___x_1419_, v___x_1606_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1607_);
v___x_1609_ = v___x_1344_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
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
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_a_1336_);
lean_del_object(v___x_1319_);
lean_dec(v_name_1317_);
v_a_1621_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1338_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1338_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_del_object(v___x_1319_);
lean_dec(v_name_1317_);
lean_dec_ref(v_params_1304_);
v_a_1629_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1335_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1335_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___boxed(lean_object* v_indVal_1663_, lean_object* v_params_1664_, lean_object* v_encInstBinders_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(v_indVal_1663_, v_params_1664_, v_encInstBinders_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec_ref(v_encInstBinders_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(lean_object* v_00_u03b1_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___boxed(lean_object* v_00_u03b1_1684_, lean_object* v_msg_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(v_00_u03b1_1684_, v_msg_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(size_t v_sz_1694_, size_t v_i_1695_, lean_object* v_bs_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_1694_, v_i_1695_, v_bs_1696_, v___y_1699_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___boxed(lean_object* v_sz_1705_, lean_object* v_i_1706_, lean_object* v_bs_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1705_);
lean_dec(v_sz_1705_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1706_);
lean_dec(v_i_1706_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(lean_object* v_cls_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v_cls_1718_, v_msg_1719_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___boxed(lean_object* v_cls_1728_, lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(v_cls_1728_, v_msg_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1(lean_object* v_msgData_1738_, lean_object* v_macroStack_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg(v_msgData_1738_, v_macroStack_1739_, v___y_1744_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___boxed(lean_object* v_msgData_1748_, lean_object* v_macroStack_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1(v_msgData_1748_, v_macroStack_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
return v_res_1757_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = l_Lean_Parser_termParser(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0);
v___x_1761_ = l_Lean_Parser_Term_matchAlt(v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm(void){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(lean_object* v_s_1763_){
_start:
{
lean_inc(v_s_1763_);
return v_s_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed(lean_object* v_s_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(v_s_1764_);
lean_dec(v_s_1764_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(lean_object* v___x_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_toCold_1772_; lean_object* v_currMacroScope_1773_; lean_object* v_quotContext_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_toCold_1772_ = lean_ctor_get(v___y_1769_, 0);
lean_inc_ref(v_toCold_1772_);
v_currMacroScope_1773_ = lean_ctor_get(v___y_1769_, 9);
lean_inc(v_currMacroScope_1773_);
lean_dec_ref(v___y_1769_);
v_quotContext_1774_ = lean_ctor_get(v_toCold_1772_, 2);
lean_inc(v_quotContext_1774_);
lean_dec_ref(v_toCold_1772_);
v___x_1775_ = l_Lean_addMacroScope(v_quotContext_1774_, v___x_1768_, v_currMacroScope_1773_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed(lean_object* v___x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(v___x_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___f_1790_; lean_object* v___x_1791_; 
v___f_1790_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2));
v___x_1791_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_1790_, v___y_1787_, v___y_1788_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___boxed(lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(v___y_1800_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___boxed(lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0(lean_object* v_k_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v_b_1815_, lean_object* v_c_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
v___x_1822_ = lean_apply_9(v_k_1812_, v_b_1815_, v_c_1816_, v___y_1813_, v___y_1814_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, lean_box(0));
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0___boxed(lean_object* v_k_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v_b_1826_, lean_object* v_c_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0(v_k_1823_, v___y_1824_, v___y_1825_, v_b_1826_, v_c_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(lean_object* v_type_1834_, lean_object* v_k_1835_, uint8_t v_cleanupAnnotations_1836_, uint8_t v_whnfType_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___f_1845_; lean_object* v___x_1846_; 
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1845_, 0, v_k_1835_);
lean_closure_set(v___f_1845_, 1, v___y_1838_);
lean_closure_set(v___f_1845_, 2, v___y_1839_);
v___x_1846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1834_, v___f_1845_, v_cleanupAnnotations_1836_, v_whnfType_1837_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1846_) == 0)
{
return v___x_1846_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg___boxed(lean_object* v_type_1855_, lean_object* v_k_1856_, lean_object* v_cleanupAnnotations_1857_, lean_object* v_whnfType_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1866_; uint8_t v_whnfType_boxed_1867_; lean_object* v_res_1868_; 
v_cleanupAnnotations_boxed_1866_ = lean_unbox(v_cleanupAnnotations_1857_);
v_whnfType_boxed_1867_ = lean_unbox(v_whnfType_1858_);
v_res_1868_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(v_type_1855_, v_k_1856_, v_cleanupAnnotations_boxed_1866_, v_whnfType_boxed_1867_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(lean_object* v_00_u03b1_1869_, lean_object* v_type_1870_, lean_object* v_k_1871_, uint8_t v_cleanupAnnotations_1872_, uint8_t v_whnfType_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(v_type_1870_, v_k_1871_, v_cleanupAnnotations_1872_, v_whnfType_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_type_1883_, lean_object* v_k_1884_, lean_object* v_cleanupAnnotations_1885_, lean_object* v_whnfType_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1894_; uint8_t v_whnfType_boxed_1895_; lean_object* v_res_1896_; 
v_cleanupAnnotations_boxed_1894_ = lean_unbox(v_cleanupAnnotations_1885_);
v_whnfType_boxed_1895_ = lean_unbox(v_whnfType_1886_);
v_res_1896_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(v_00_u03b1_1882_, v_type_1883_, v_k_1884_, v_cleanupAnnotations_boxed_1894_, v_whnfType_boxed_1895_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_bs_1899_){
_start:
{
uint8_t v___x_1900_; 
v___x_1900_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1900_ == 0)
{
return v_bs_1899_;
}
else
{
lean_object* v_v_1901_; lean_object* v___x_1902_; lean_object* v_bs_x27_1903_; size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; 
v_v_1901_ = lean_array_uget(v_bs_1899_, v_i_1898_);
v___x_1902_ = lean_unsigned_to_nat(0u);
v_bs_x27_1903_ = lean_array_uset(v_bs_1899_, v_i_1898_, v___x_1902_);
v___x_1904_ = ((size_t)1ULL);
v___x_1905_ = lean_usize_add(v_i_1898_, v___x_1904_);
v___x_1906_ = lean_array_uset(v_bs_x27_1903_, v_i_1898_, v_v_1901_);
v_i_1898_ = v___x_1905_;
v_bs_1899_ = v___x_1906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15___boxed(lean_object* v_sz_1908_, lean_object* v_i_1909_, lean_object* v_bs_1910_){
_start:
{
size_t v_sz_boxed_1911_; size_t v_i_boxed_1912_; lean_object* v_res_1913_; 
v_sz_boxed_1911_ = lean_unbox_usize(v_sz_1908_);
lean_dec(v_sz_1908_);
v_i_boxed_1912_ = lean_unbox_usize(v_i_1909_);
lean_dec(v_i_1909_);
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(v_sz_boxed_1911_, v_i_boxed_1912_, v_bs_1910_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(size_t v_sz_1914_, size_t v_i_1915_, lean_object* v_bs_1916_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_lt(v_i_1915_, v_sz_1914_);
if (v___x_1917_ == 0)
{
return v_bs_1916_;
}
else
{
lean_object* v_v_1918_; lean_object* v___x_1919_; lean_object* v_bs_x27_1920_; size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_v_1918_ = lean_array_uget(v_bs_1916_, v_i_1915_);
v___x_1919_ = lean_unsigned_to_nat(0u);
v_bs_x27_1920_ = lean_array_uset(v_bs_1916_, v_i_1915_, v___x_1919_);
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1915_, v___x_1921_);
v___x_1923_ = lean_array_uset(v_bs_x27_1920_, v_i_1915_, v_v_1918_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12_spec__15(v_sz_1914_, v___x_1922_, v___x_1923_);
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___boxed(lean_object* v_sz_1925_, lean_object* v_i_1926_, lean_object* v_bs_1927_){
_start:
{
size_t v_sz_boxed_1928_; size_t v_i_boxed_1929_; lean_object* v_res_1930_; 
v_sz_boxed_1928_ = lean_unbox_usize(v_sz_1925_);
lean_dec(v_sz_1925_);
v_i_boxed_1929_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(v_sz_boxed_1928_, v_i_boxed_1929_, v_bs_1927_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(size_t v_sz_1931_, size_t v_i_1932_, lean_object* v_bs_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1932_, v_sz_1931_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_bs_1933_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v_bs_x27_1946_; lean_object* v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = lean_unsigned_to_nat(0u);
v_bs_x27_1946_ = lean_array_uset(v_bs_1933_, v_i_1932_, v___x_1945_);
v___x_1947_ = l_Lean_mkIdent(v_a_1944_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1932_, v___x_1948_);
v___x_1950_ = lean_array_uset(v_bs_x27_1946_, v_i_1932_, v___x_1947_);
v_i_1932_ = v___x_1949_;
v_bs_1933_ = v___x_1950_;
goto _start;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_bs_1933_);
v_a_1952_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1943_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5___boxed(lean_object* v_sz_1960_, lean_object* v_i_1961_, lean_object* v_bs_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
size_t v_sz_boxed_1970_; size_t v_i_boxed_1971_; lean_object* v_res_1972_; 
v_sz_boxed_1970_ = lean_unbox_usize(v_sz_1960_);
lean_dec(v_sz_1960_);
v_i_boxed_1971_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(v_sz_boxed_1970_, v_i_boxed_1971_, v_bs_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(size_t v_sz_1973_, size_t v_i_1974_, lean_object* v_bs_1975_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_usize_dec_lt(v_i_1974_, v_sz_1973_);
if (v___x_1976_ == 0)
{
return v_bs_1975_;
}
else
{
lean_object* v_v_1977_; lean_object* v___x_1978_; lean_object* v_bs_x27_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v_v_1977_ = lean_array_uget(v_bs_1975_, v_i_1974_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v_bs_x27_1979_ = lean_array_uset(v_bs_1975_, v_i_1974_, v___x_1978_);
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1974_, v___x_1980_);
v___x_1982_ = lean_array_uset(v_bs_x27_1979_, v_i_1974_, v_v_1977_);
v_i_1974_ = v___x_1981_;
v_bs_1975_ = v___x_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3___boxed(lean_object* v_sz_1984_, lean_object* v_i_1985_, lean_object* v_bs_1986_){
_start:
{
size_t v_sz_boxed_1987_; size_t v_i_boxed_1988_; lean_object* v_res_1989_; 
v_sz_boxed_1987_ = lean_unbox_usize(v_sz_1984_);
lean_dec(v_sz_1984_);
v_i_boxed_1988_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(v_sz_boxed_1987_, v_i_boxed_1988_, v_bs_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_bs_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_bs_1992_);
return v___x_1996_;
}
else
{
lean_object* v_toCold_1997_; lean_object* v_ref_1998_; lean_object* v_currMacroScope_1999_; lean_object* v_quotContext_2000_; lean_object* v_v_2001_; lean_object* v___x_2002_; lean_object* v_bs_x27_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v_toCold_1997_ = lean_ctor_get(v___y_1993_, 0);
v_ref_1998_ = lean_ctor_get(v___y_1993_, 4);
v_currMacroScope_1999_ = lean_ctor_get(v___y_1993_, 9);
v_quotContext_2000_ = lean_ctor_get(v_toCold_1997_, 2);
v_v_2001_ = lean_array_uget(v_bs_1992_, v_i_1991_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v_bs_x27_2003_ = lean_array_uset(v_bs_1992_, v_i_1991_, v___x_2002_);
v___x_2004_ = 0;
v___x_2005_ = l_Lean_SourceInfo_fromRef(v_ref_1998_, v___x_2004_);
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2005_, 5);
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2005_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_2011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39);
v___x_2012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(v_currMacroScope_1999_);
lean_inc(v_quotContext_2000_);
v___x_2013_ = l_Lean_addMacroScope(v_quotContext_2000_, v___x_2012_, v_currMacroScope_1999_);
v___x_2014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43));
v___x_2015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2005_);
lean_ctor_set(v___x_2015_, 1, v___x_2011_);
lean_ctor_set(v___x_2015_, 2, v___x_2013_);
lean_ctor_set(v___x_2015_, 3, v___x_2014_);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2017_ = l_Lean_Syntax_node1(v___x_2005_, v___x_2016_, v_v_2001_);
v___x_2018_ = l_Lean_Syntax_node2(v___x_2005_, v___x_2010_, v___x_2015_, v___x_2017_);
v___x_2019_ = l_Lean_Syntax_node1(v___x_2005_, v___x_2009_, v___x_2018_);
v___x_2020_ = l_Lean_Syntax_node2(v___x_2005_, v___x_2006_, v___x_2008_, v___x_2019_);
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_1991_, v___x_2021_);
v___x_2023_ = lean_array_uset(v_bs_x27_2003_, v_i_1991_, v___x_2020_);
v_i_1991_ = v___x_2022_;
v_bs_1992_ = v___x_2023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg___boxed(lean_object* v_sz_2025_, lean_object* v_i_2026_, lean_object* v_bs_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
size_t v_sz_boxed_2030_; size_t v_i_boxed_2031_; lean_object* v_res_2032_; 
v_sz_boxed_2030_ = lean_unbox_usize(v_sz_2025_);
lean_dec(v_sz_2025_);
v_i_boxed_2031_ = lean_unbox_usize(v_i_2026_);
lean_dec(v_i_2026_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(v_sz_boxed_2030_, v_i_boxed_2031_, v_bs_2027_, v___y_2028_);
lean_dec_ref(v___y_2028_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_bs_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_usize_dec_lt(v_i_2034_, v_sz_2033_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_bs_2035_);
return v___x_2044_;
}
else
{
lean_object* v_toCold_2045_; lean_object* v_ref_2046_; lean_object* v_currMacroScope_2047_; lean_object* v_quotContext_2048_; lean_object* v_v_2049_; lean_object* v___x_2050_; lean_object* v_bs_x27_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_toCold_2045_ = lean_ctor_get(v___y_2040_, 0);
v_ref_2046_ = lean_ctor_get(v___y_2040_, 4);
v_currMacroScope_2047_ = lean_ctor_get(v___y_2040_, 9);
v_quotContext_2048_ = lean_ctor_get(v_toCold_2045_, 2);
v_v_2049_ = lean_array_uget(v_bs_2035_, v_i_2034_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v_bs_x27_2051_ = lean_array_uset(v_bs_2035_, v_i_2034_, v___x_2050_);
v___x_2052_ = 0;
v___x_2053_ = l_Lean_SourceInfo_fromRef(v_ref_2046_, v___x_2052_);
v___x_2054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2053_, 5);
v___x_2056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_2059_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(v_currMacroScope_2047_);
lean_inc(v_quotContext_2048_);
v___x_2061_ = l_Lean_addMacroScope(v_quotContext_2048_, v___x_2060_, v_currMacroScope_2047_);
v___x_2062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43));
v___x_2063_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2053_);
lean_ctor_set(v___x_2063_, 1, v___x_2059_);
lean_ctor_set(v___x_2063_, 2, v___x_2061_);
lean_ctor_set(v___x_2063_, 3, v___x_2062_);
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2065_ = l_Lean_Syntax_node1(v___x_2053_, v___x_2064_, v_v_2049_);
v___x_2066_ = l_Lean_Syntax_node2(v___x_2053_, v___x_2058_, v___x_2063_, v___x_2065_);
v___x_2067_ = l_Lean_Syntax_node1(v___x_2053_, v___x_2057_, v___x_2066_);
v___x_2068_ = l_Lean_Syntax_node2(v___x_2053_, v___x_2054_, v___x_2056_, v___x_2067_);
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_add(v_i_2034_, v___x_2069_);
v___x_2071_ = lean_array_uset(v_bs_x27_2051_, v_i_2034_, v___x_2068_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(v_sz_2033_, v___x_2070_, v___x_2071_, v___y_2040_);
return v___x_2072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8___boxed(lean_object* v_sz_2073_, lean_object* v_i_2074_, lean_object* v_bs_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2073_);
lean_dec(v_sz_2073_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(v_sz_boxed_2083_, v_i_boxed_2084_, v_bs_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(size_t v_sz_2086_, size_t v_i_2087_, lean_object* v_bs_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_usize_dec_lt(v_i_2087_, v_sz_2086_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_bs_2088_);
return v___x_2092_;
}
else
{
lean_object* v_toCold_2093_; lean_object* v_ref_2094_; lean_object* v_currMacroScope_2095_; lean_object* v_quotContext_2096_; lean_object* v_v_2097_; lean_object* v___x_2098_; lean_object* v_bs_x27_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v_toCold_2093_ = lean_ctor_get(v___y_2089_, 0);
v_ref_2094_ = lean_ctor_get(v___y_2089_, 4);
v_currMacroScope_2095_ = lean_ctor_get(v___y_2089_, 9);
v_quotContext_2096_ = lean_ctor_get(v_toCold_2093_, 2);
v_v_2097_ = lean_array_uget(v_bs_2088_, v_i_2087_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v_bs_x27_2099_ = lean_array_uset(v_bs_2088_, v_i_2087_, v___x_2098_);
v___x_2100_ = 0;
v___x_2101_ = l_Lean_SourceInfo_fromRef(v_ref_2094_, v___x_2100_);
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2101_, 5);
v___x_2104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2101_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_2107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23);
v___x_2108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24));
lean_inc(v_currMacroScope_2095_);
lean_inc(v_quotContext_2096_);
v___x_2109_ = l_Lean_addMacroScope(v_quotContext_2096_, v___x_2108_, v_currMacroScope_2095_);
v___x_2110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
v___x_2111_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2101_);
lean_ctor_set(v___x_2111_, 1, v___x_2107_);
lean_ctor_set(v___x_2111_, 2, v___x_2109_);
lean_ctor_set(v___x_2111_, 3, v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2113_ = l_Lean_Syntax_node1(v___x_2101_, v___x_2112_, v_v_2097_);
v___x_2114_ = l_Lean_Syntax_node2(v___x_2101_, v___x_2106_, v___x_2111_, v___x_2113_);
v___x_2115_ = l_Lean_Syntax_node1(v___x_2101_, v___x_2105_, v___x_2114_);
v___x_2116_ = l_Lean_Syntax_node2(v___x_2101_, v___x_2102_, v___x_2104_, v___x_2115_);
v___x_2117_ = ((size_t)1ULL);
v___x_2118_ = lean_usize_add(v_i_2087_, v___x_2117_);
v___x_2119_ = lean_array_uset(v_bs_x27_2099_, v_i_2087_, v___x_2116_);
v_i_2087_ = v___x_2118_;
v_bs_2088_ = v___x_2119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg___boxed(lean_object* v_sz_2121_, lean_object* v_i_2122_, lean_object* v_bs_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2121_);
lean_dec(v_sz_2121_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2122_);
lean_dec(v_i_2122_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(v_sz_boxed_2126_, v_i_boxed_2127_, v_bs_2123_, v___y_2124_);
lean_dec_ref(v___y_2124_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(size_t v_sz_2129_, size_t v_i_2130_, lean_object* v_bs_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_2139_; 
v___x_2139_ = lean_usize_dec_lt(v_i_2130_, v_sz_2129_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_bs_2131_);
return v___x_2140_;
}
else
{
lean_object* v_toCold_2141_; lean_object* v_ref_2142_; lean_object* v_currMacroScope_2143_; lean_object* v_quotContext_2144_; lean_object* v_v_2145_; lean_object* v___x_2146_; lean_object* v_bs_x27_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_toCold_2141_ = lean_ctor_get(v___y_2136_, 0);
v_ref_2142_ = lean_ctor_get(v___y_2136_, 4);
v_currMacroScope_2143_ = lean_ctor_get(v___y_2136_, 9);
v_quotContext_2144_ = lean_ctor_get(v_toCold_2141_, 2);
v_v_2145_ = lean_array_uget(v_bs_2131_, v_i_2130_);
v___x_2146_ = lean_unsigned_to_nat(0u);
v_bs_x27_2147_ = lean_array_uset(v_bs_2131_, v_i_2130_, v___x_2146_);
v___x_2148_ = 0;
v___x_2149_ = l_Lean_SourceInfo_fromRef(v_ref_2142_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
lean_inc_n(v___x_2149_, 5);
v___x_2152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2149_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_2154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_2155_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23);
v___x_2156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24));
lean_inc(v_currMacroScope_2143_);
lean_inc(v_quotContext_2144_);
v___x_2157_ = l_Lean_addMacroScope(v_quotContext_2144_, v___x_2156_, v_currMacroScope_2143_);
v___x_2158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
v___x_2159_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2149_);
lean_ctor_set(v___x_2159_, 1, v___x_2155_);
lean_ctor_set(v___x_2159_, 2, v___x_2157_);
lean_ctor_set(v___x_2159_, 3, v___x_2158_);
v___x_2160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2161_ = l_Lean_Syntax_node1(v___x_2149_, v___x_2160_, v_v_2145_);
v___x_2162_ = l_Lean_Syntax_node2(v___x_2149_, v___x_2154_, v___x_2159_, v___x_2161_);
v___x_2163_ = l_Lean_Syntax_node1(v___x_2149_, v___x_2153_, v___x_2162_);
v___x_2164_ = l_Lean_Syntax_node2(v___x_2149_, v___x_2150_, v___x_2152_, v___x_2163_);
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_add(v_i_2130_, v___x_2165_);
v___x_2167_ = lean_array_uset(v_bs_x27_2147_, v_i_2130_, v___x_2164_);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(v_sz_2129_, v___x_2166_, v___x_2167_, v___y_2136_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7___boxed(lean_object* v_sz_2169_, lean_object* v_i_2170_, lean_object* v_bs_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
size_t v_sz_boxed_2179_; size_t v_i_boxed_2180_; lean_object* v_res_2181_; 
v_sz_boxed_2179_ = lean_unbox_usize(v_sz_2169_);
lean_dec(v_sz_2169_);
v_i_boxed_2180_ = lean_unbox_usize(v_i_2170_);
lean_dec(v_i_2170_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(v_sz_boxed_2179_, v_i_boxed_2180_, v_bs_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(size_t v_sz_2182_, size_t v_i_2183_, lean_object* v_bs_2184_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2183_, v_sz_2182_);
if (v___x_2185_ == 0)
{
return v_bs_2184_;
}
else
{
lean_object* v_v_2186_; lean_object* v___x_2187_; lean_object* v_bs_x27_2188_; size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v_v_2186_ = lean_array_uget(v_bs_2184_, v_i_2183_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v_bs_x27_2188_ = lean_array_uset(v_bs_2184_, v_i_2183_, v___x_2187_);
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2183_, v___x_2189_);
v___x_2191_ = lean_array_uset(v_bs_x27_2188_, v_i_2183_, v_v_2186_);
v_i_2183_ = v___x_2190_;
v_bs_2184_ = v___x_2191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2___boxed(lean_object* v_sz_2193_, lean_object* v_i_2194_, lean_object* v_bs_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2193_);
lean_dec(v_sz_2193_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2194_);
lean_dec(v_i_2194_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(v_sz_boxed_2196_, v_i_boxed_2197_, v_bs_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(size_t v_sz_2199_, size_t v_i_2200_, lean_object* v_bs_2201_){
_start:
{
uint8_t v___x_2202_; 
v___x_2202_ = lean_usize_dec_lt(v_i_2200_, v_sz_2199_);
if (v___x_2202_ == 0)
{
return v_bs_2201_;
}
else
{
lean_object* v_v_2203_; lean_object* v___x_2204_; lean_object* v_bs_x27_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v_v_2203_ = lean_array_uget(v_bs_2201_, v_i_2200_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v_bs_x27_2205_ = lean_array_uset(v_bs_2201_, v_i_2200_, v___x_2204_);
v___x_2206_ = ((size_t)1ULL);
v___x_2207_ = lean_usize_add(v_i_2200_, v___x_2206_);
v___x_2208_ = lean_array_uset(v_bs_x27_2205_, v_i_2200_, v_v_2203_);
v_i_2200_ = v___x_2207_;
v_bs_2201_ = v___x_2208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6___boxed(lean_object* v_sz_2210_, lean_object* v_i_2211_, lean_object* v_bs_2212_){
_start:
{
size_t v_sz_boxed_2213_; size_t v_i_boxed_2214_; lean_object* v_res_2215_; 
v_sz_boxed_2213_ = lean_unbox_usize(v_sz_2210_);
lean_dec(v_sz_2210_);
v_i_boxed_2214_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(v_sz_boxed_2213_, v_i_boxed_2214_, v_bs_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(size_t v_sz_2216_, size_t v_i_2217_, lean_object* v_bs_2218_){
_start:
{
uint8_t v___x_2219_; 
v___x_2219_ = lean_usize_dec_lt(v_i_2217_, v_sz_2216_);
if (v___x_2219_ == 0)
{
return v_bs_2218_;
}
else
{
lean_object* v_v_2220_; lean_object* v___x_2221_; lean_object* v_bs_x27_2222_; size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v_v_2220_ = lean_array_uget(v_bs_2218_, v_i_2217_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v_bs_x27_2222_ = lean_array_uset(v_bs_2218_, v_i_2217_, v___x_2221_);
v___x_2223_ = ((size_t)1ULL);
v___x_2224_ = lean_usize_add(v_i_2217_, v___x_2223_);
v___x_2225_ = lean_array_uset(v_bs_x27_2222_, v_i_2217_, v_v_2220_);
v_i_2217_ = v___x_2224_;
v_bs_2218_ = v___x_2225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4___boxed(lean_object* v_sz_2227_, lean_object* v_i_2228_, lean_object* v_bs_2229_){
_start:
{
size_t v_sz_boxed_2230_; size_t v_i_boxed_2231_; lean_object* v_res_2232_; 
v_sz_boxed_2230_ = lean_unbox_usize(v_sz_2227_);
lean_dec(v_sz_2227_);
v_i_boxed_2231_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v_res_2232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(v_sz_boxed_2230_, v_i_boxed_2231_, v_bs_2229_);
return v_res_2232_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__2));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(size_t v_sz_2242_, size_t v_i_2243_, lean_object* v_bs_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_usize_dec_lt(v_i_2243_, v_sz_2242_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_bs_2244_);
return v___x_2253_;
}
else
{
lean_object* v_v_2254_; lean_object* v___x_2255_; 
v_v_2254_ = lean_array_uget_borrowed(v_bs_2244_, v_i_2243_);
v___x_2255_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_v_2254_, v___y_2247_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; lean_object* v_bs_x27_2258_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2257_ = lean_unsigned_to_nat(0u);
v_bs_x27_2258_ = lean_array_uset(v_bs_2244_, v_i_2243_, v___x_2257_);
v___x_2259_ = l_Lean_LocalDecl_userName(v_a_2256_);
lean_dec(v_a_2256_);
v___x_2291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__85));
v___x_2292_ = lean_name_eq(v___x_2259_, v___x_2291_);
if (v___x_2292_ == 0)
{
v___y_2261_ = v___y_2249_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__3);
v___x_2294_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_2293_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref_known(v___x_2294_, 1);
v___y_2261_ = v___y_2249_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v___x_2259_);
lean_dec_ref(v_bs_x27_2258_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
v___jp_2260_:
{
lean_object* v_toCold_2262_; lean_object* v_ref_2263_; lean_object* v_currMacroScope_2264_; lean_object* v_quotContext_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; 
v_toCold_2262_ = lean_ctor_get(v___y_2261_, 0);
v_ref_2263_ = lean_ctor_get(v___y_2261_, 4);
v_currMacroScope_2264_ = lean_ctor_get(v___y_2261_, 9);
v_quotContext_2265_ = lean_ctor_get(v_toCold_2262_, 2);
v___x_2266_ = 0;
v___x_2267_ = l_Lean_SourceInfo_fromRef(v_ref_2263_, v___x_2266_);
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___closed__1));
v___x_2269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc_n(v___x_2267_, 7);
v___x_2270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2267_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2272_ = l_Lean_mkIdent(v___x_2259_);
v___x_2273_ = l_Lean_Syntax_node1(v___x_2267_, v___x_2271_, v___x_2272_);
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_2275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2267_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3);
v___x_2277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4));
lean_inc(v_currMacroScope_2264_);
lean_inc(v_quotContext_2265_);
v___x_2278_ = l_Lean_addMacroScope(v_quotContext_2265_, v___x_2277_, v_currMacroScope_2264_);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
v___x_2280_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2267_);
lean_ctor_set(v___x_2280_, 1, v___x_2276_);
lean_ctor_set(v___x_2280_, 2, v___x_2278_);
lean_ctor_set(v___x_2280_, 3, v___x_2279_);
v___x_2281_ = l_Lean_Syntax_node2(v___x_2267_, v___x_2271_, v___x_2275_, v___x_2280_);
v___x_2282_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_2283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2267_);
lean_ctor_set(v___x_2283_, 1, v___x_2271_);
lean_ctor_set(v___x_2283_, 2, v___x_2282_);
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
v___x_2285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2267_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = l_Lean_Syntax_node5(v___x_2267_, v___x_2268_, v___x_2270_, v___x_2273_, v___x_2281_, v___x_2283_, v___x_2285_);
v___x_2287_ = ((size_t)1ULL);
v___x_2288_ = lean_usize_add(v_i_2243_, v___x_2287_);
v___x_2289_ = lean_array_uset(v_bs_x27_2258_, v_i_2243_, v___x_2286_);
v_i_2243_ = v___x_2288_;
v_bs_2244_ = v___x_2289_;
goto _start;
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_bs_2244_);
v_a_2303_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2255_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2255_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___boxed(lean_object* v_sz_2311_, lean_object* v_i_2312_, lean_object* v_bs_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
size_t v_sz_boxed_2321_; size_t v_i_boxed_2322_; lean_object* v_res_2323_; 
v_sz_boxed_2321_ = lean_unbox_usize(v_sz_2311_);
lean_dec(v_sz_2311_);
v_i_boxed_2322_ = lean_unbox_usize(v_i_2312_);
lean_dec(v_i_2312_);
v_res_2323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(v_sz_boxed_2321_, v_i_boxed_2322_, v_bs_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2323_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__10));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1(lean_object* v_v_2353_, lean_object* v___f_2354_, lean_object* v___x_2355_, lean_object* v___x_2356_, lean_object* v_argVars_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
if (lean_obj_tag(v_v_2353_) == 1)
{
lean_object* v_str_2366_; size_t v_sz_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v_str_2366_ = lean_ctor_get(v_v_2353_, 1);
lean_inc_ref(v_str_2366_);
lean_dec_ref_known(v_v_2353_, 2);
v_sz_2367_ = lean_array_size(v_argVars_2357_);
v___x_2368_ = ((size_t)0ULL);
lean_inc_ref(v_argVars_2357_);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(v_sz_2367_, v___x_2368_, v_argVars_2357_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_toCold_2370_; lean_object* v_a_2371_; lean_object* v_ref_2372_; lean_object* v_currMacroScope_2373_; lean_object* v_quotContext_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; size_t v_sz_2387_; lean_object* v___x_2388_; size_t v_sz_2389_; lean_object* v___x_2390_; size_t v_sz_2391_; lean_object* v___x_2392_; size_t v_sz_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_toCold_2370_ = lean_ctor_get(v___y_2363_, 0);
v_a_2371_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2369_, 1);
v_ref_2372_ = lean_ctor_get(v___y_2363_, 4);
v_currMacroScope_2373_ = lean_ctor_get(v___y_2363_, 9);
v_quotContext_2374_ = lean_ctor_get(v_toCold_2370_, 2);
v___x_2375_ = 0;
v___x_2376_ = l_Lean_SourceInfo_fromRef(v_ref_2372_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0));
v___x_2378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2));
v___x_2379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__1));
v___x_2380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2381_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
lean_inc_n(v___x_2376_, 3);
v___x_2382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2376_);
lean_ctor_set(v___x_2382_, 1, v___x_2380_);
lean_ctor_set(v___x_2382_, 2, v___x_2381_);
v___x_2383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__2));
v___x_2384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2376_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
lean_inc_ref_n(v___x_2382_, 7);
v___x_2386_ = l_Lean_Syntax_node7(v___x_2376_, v___x_2385_, v___x_2382_, v___x_2382_, v___x_2382_, v___x_2382_, v___x_2382_, v___x_2382_, v___x_2382_);
v_sz_2387_ = lean_array_size(v_a_2371_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(v_sz_2387_, v___x_2368_, v_a_2371_);
v_sz_2389_ = lean_array_size(v___x_2388_);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(v_sz_2389_, v___x_2368_, v___x_2388_);
v_sz_2391_ = lean_array_size(v___x_2390_);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(v_sz_2391_, v___x_2368_, v___x_2390_);
v_sz_2393_ = lean_array_size(v___x_2392_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_2393_, v___x_2368_, v___x_2392_);
v___x_2395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(v_sz_2367_, v___x_2368_, v_argVars_2357_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; size_t v_sz_2397_; lean_object* v___x_2398_; size_t v_sz_2399_; lean_object* v___x_2400_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v_sz_2397_ = lean_array_size(v_a_2396_);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(v_sz_2397_, v___x_2368_, v_a_2396_);
v_sz_2399_ = lean_array_size(v___x_2398_);
lean_inc_ref(v___x_2398_);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(v_sz_2399_, v___x_2368_, v___x_2398_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
lean_inc_ref(v___f_2354_);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2362_);
lean_inc_ref(v___y_2361_);
lean_inc(v___y_2360_);
lean_inc_ref(v___y_2359_);
v___x_2402_ = lean_apply_7(v___f_2354_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, lean_box(0));
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc_n(v_a_2403_, 20);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = l_Array_append___redArg(v___x_2381_, v___x_2394_);
lean_dec_ref(v___x_2394_);
lean_inc_n(v___x_2376_, 5);
v___x_2405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2376_);
lean_ctor_set(v___x_2405_, 1, v___x_2380_);
lean_ctor_set(v___x_2405_, 2, v___x_2404_);
v___x_2406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_2407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2376_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15);
v___x_2409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_2410_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
lean_inc_n(v_currMacroScope_2373_, 3);
lean_inc_n(v_quotContext_2374_, 3);
v___x_2411_ = l_Lean_addMacroScope(v_quotContext_2374_, v___x_2410_, v_currMacroScope_2373_);
v___x_2412_ = lean_box(0);
lean_inc(v___x_2411_);
v___x_2413_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2376_);
lean_ctor_set(v___x_2413_, 1, v___x_2408_);
lean_ctor_set(v___x_2413_, 2, v___x_2411_);
lean_ctor_set(v___x_2413_, 3, v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10));
v___x_2415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_2416_ = l_Lean_Syntax_node2(v___x_2376_, v___x_2415_, v___x_2407_, v___x_2413_);
v___x_2417_ = l_Lean_Syntax_node1(v___x_2376_, v___x_2380_, v___x_2416_);
v___x_2418_ = lean_box(0);
v___x_2419_ = l_Lean_Name_str___override(v___x_2418_, v_str_2366_);
v___x_2420_ = l_Lean_mkIdent(v___x_2419_);
v___x_2421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25));
v___x_2422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__4));
v___x_2423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_a_2403_);
lean_ctor_set(v___x_2423_, 1, v___x_2383_);
v___x_2424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_2425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__6));
v___x_2426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34));
v___x_2427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_a_2403_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
lean_inc(v___x_2420_);
v___x_2428_ = l_Lean_Syntax_node2(v_a_2403_, v___x_2425_, v___x_2427_, v___x_2420_);
v___x_2429_ = l_Array_append___redArg(v___x_2381_, v___x_2398_);
lean_inc_ref(v___x_2429_);
v___x_2430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2403_);
lean_ctor_set(v___x_2430_, 1, v___x_2380_);
lean_ctor_set(v___x_2430_, 2, v___x_2429_);
lean_inc(v___x_2428_);
v___x_2431_ = l_Lean_Syntax_node2(v_a_2403_, v___x_2424_, v___x_2428_, v___x_2430_);
v___x_2432_ = l_Lean_Syntax_node1(v_a_2403_, v___x_2380_, v___x_2431_);
v___x_2433_ = l_Lean_Syntax_node1(v_a_2403_, v___x_2380_, v___x_2432_);
v___x_2434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__7));
v___x_2435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2403_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101));
v___x_2437_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102));
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v_a_2403_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104);
v___x_2440_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105));
v___x_2441_ = l_Lean_addMacroScope(v_quotContext_2374_, v___x_2440_, v_currMacroScope_2373_);
v___x_2442_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108));
v___x_2443_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2443_, 0, v_a_2403_);
lean_ctor_set(v___x_2443_, 1, v___x_2439_);
lean_ctor_set(v___x_2443_, 2, v___x_2441_);
lean_ctor_set(v___x_2443_, 3, v___x_2442_);
v___x_2444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__9));
v___x_2445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
v___x_2446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
v___x_2447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_a_2403_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57));
v___x_2449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58);
v___x_2450_ = l_Lean_addMacroScope(v_quotContext_2374_, v___x_2418_, v_currMacroScope_2373_);
v___x_2451_ = l_Lean_Name_mkStr3(v___x_2377_, v___x_2421_, v___x_2355_);
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
v___x_2453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62));
lean_inc_ref_n(v___x_2356_, 2);
v___x_2454_ = l_Lean_Name_mkStr3(v___x_2377_, v___x_2356_, v___x_2414_);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
v___x_2456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67));
v___x_2457_ = l_Lean_Name_mkStr3(v___x_2377_, v___x_2356_, v___x_2378_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = l_Lean_Name_mkStr2(v___x_2377_, v___x_2356_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
v___x_2461_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57));
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2458_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2456_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2455_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2453_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2452_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
lean_inc_ref(v___x_2467_);
lean_inc(v___x_2450_);
v___x_2468_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2468_, 0, v_a_2403_);
lean_ctor_set(v___x_2468_, 1, v___x_2449_);
lean_ctor_set(v___x_2468_, 2, v___x_2450_);
lean_ctor_set(v___x_2468_, 3, v___x_2467_);
v___x_2469_ = l_Lean_Syntax_node1(v_a_2403_, v___x_2448_, v___x_2468_);
v___x_2470_ = l_Lean_Syntax_node2(v_a_2403_, v___x_2445_, v___x_2447_, v___x_2469_);
v___x_2471_ = l_Array_append___redArg(v___x_2381_, v_a_2401_);
lean_dec(v_a_2401_);
v___x_2472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2403_);
lean_ctor_set(v___x_2472_, 1, v___x_2380_);
lean_ctor_set(v___x_2472_, 2, v___x_2471_);
v___x_2473_ = l_Lean_Syntax_node2(v_a_2403_, v___x_2424_, v___x_2428_, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2403_);
lean_ctor_set(v___x_2474_, 1, v___x_2406_);
v___x_2475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2403_);
lean_ctor_set(v___x_2475_, 1, v___x_2408_);
lean_ctor_set(v___x_2475_, 2, v___x_2411_);
lean_ctor_set(v___x_2475_, 3, v___x_2412_);
v___x_2476_ = l_Lean_Syntax_node1(v_a_2403_, v___x_2380_, v___x_2475_);
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(v_sz_2399_, v___x_2368_, v___x_2398_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2362_);
lean_inc_ref(v___y_2361_);
lean_inc(v___y_2360_);
lean_inc_ref(v___y_2359_);
v___x_2479_ = lean_apply_7(v___f_2354_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, lean_box(0));
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2521_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2521_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2521_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc_n(v_a_2403_, 6);
v___x_2485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_a_2403_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l_Lean_Syntax_node5(v_a_2403_, v___x_2444_, v___x_2470_, v___x_2473_, v___x_2474_, v___x_2476_, v___x_2485_);
v___x_2487_ = l_Lean_Syntax_node1(v_a_2403_, v___x_2380_, v___x_2486_);
v___x_2488_ = l_Lean_Syntax_node2(v_a_2403_, v___x_2424_, v___x_2443_, v___x_2487_);
v___x_2489_ = l_Lean_Syntax_node1(v_a_2403_, v___x_2380_, v___x_2488_);
lean_inc(v___x_2376_);
v___x_2490_ = l_Lean_Syntax_node2(v___x_2376_, v___x_2409_, v___x_2405_, v___x_2417_);
v___x_2491_ = l_Lean_Syntax_node2(v_a_2403_, v___x_2436_, v___x_2438_, v___x_2489_);
lean_inc(v___x_2420_);
v___x_2492_ = l_Lean_Syntax_node5(v___x_2376_, v___x_2379_, v___x_2382_, v___x_2384_, v___x_2386_, v___x_2420_, v___x_2490_);
v___x_2493_ = l_Lean_Syntax_node4(v_a_2403_, v___x_2422_, v___x_2423_, v___x_2433_, v___x_2435_, v___x_2491_);
lean_inc_n(v_a_2480_, 19);
v___x_2494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2494_, 0, v_a_2480_);
lean_ctor_set(v___x_2494_, 1, v___x_2383_);
v___x_2495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2480_);
lean_ctor_set(v___x_2495_, 1, v___x_2426_);
v___x_2496_ = l_Lean_Syntax_node2(v_a_2480_, v___x_2425_, v___x_2495_, v___x_2420_);
v___x_2497_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2480_);
lean_ctor_set(v___x_2497_, 1, v___x_2380_);
lean_ctor_set(v___x_2497_, 2, v___x_2429_);
lean_inc(v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node2(v_a_2480_, v___x_2424_, v___x_2496_, v___x_2497_);
v___x_2499_ = l_Lean_Syntax_node1(v_a_2480_, v___x_2380_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_node1(v_a_2480_, v___x_2380_, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2480_);
lean_ctor_set(v___x_2501_, 1, v___x_2434_);
v___x_2502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2480_);
lean_ctor_set(v___x_2502_, 1, v___x_2437_);
v___x_2503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
v___x_2504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2480_);
lean_ctor_set(v___x_2504_, 1, v___x_2446_);
v___x_2505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2505_, 0, v_a_2480_);
lean_ctor_set(v___x_2505_, 1, v___x_2449_);
lean_ctor_set(v___x_2505_, 2, v___x_2450_);
lean_ctor_set(v___x_2505_, 3, v___x_2467_);
v___x_2506_ = l_Lean_Syntax_node1(v_a_2480_, v___x_2448_, v___x_2505_);
v___x_2507_ = l_Lean_Syntax_node2(v_a_2480_, v___x_2445_, v___x_2504_, v___x_2506_);
v___x_2508_ = l_Array_append___redArg(v___x_2381_, v_a_2478_);
lean_dec(v_a_2478_);
v___x_2509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2509_, 0, v_a_2480_);
lean_ctor_set(v___x_2509_, 1, v___x_2380_);
lean_ctor_set(v___x_2509_, 2, v___x_2508_);
v___x_2510_ = l_Lean_Syntax_node2(v_a_2480_, v___x_2424_, v___x_2496_, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_a_2480_);
lean_ctor_set(v___x_2511_, 1, v___x_2484_);
v___x_2512_ = l_Lean_Syntax_node3(v_a_2480_, v___x_2503_, v___x_2507_, v___x_2510_, v___x_2511_);
v___x_2513_ = l_Lean_Syntax_node1(v_a_2480_, v___x_2380_, v___x_2512_);
v___x_2514_ = l_Lean_Syntax_node2(v_a_2480_, v___x_2436_, v___x_2502_, v___x_2513_);
v___x_2515_ = l_Lean_Syntax_node4(v_a_2480_, v___x_2422_, v___x_2494_, v___x_2500_, v___x_2501_, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2493_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2492_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2517_);
v___x_2519_ = v___x_2482_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_a_2478_);
lean_dec(v___x_2476_);
lean_dec_ref_known(v___x_2474_, 2);
lean_dec(v___x_2473_);
lean_dec(v___x_2470_);
lean_dec_ref_known(v___x_2467_, 2);
lean_dec(v___x_2450_);
lean_dec_ref_known(v___x_2443_, 4);
lean_dec_ref_known(v___x_2438_, 2);
lean_dec_ref_known(v___x_2435_, 2);
lean_dec(v___x_2433_);
lean_dec_ref(v___x_2429_);
lean_dec_ref_known(v___x_2423_, 2);
lean_dec(v___x_2420_);
lean_dec(v___x_2417_);
lean_dec_ref_known(v___x_2405_, 3);
lean_dec(v_a_2403_);
lean_dec(v___x_2386_);
lean_dec_ref_known(v___x_2384_, 2);
lean_dec_ref_known(v___x_2382_, 3);
lean_dec(v___x_2376_);
v_a_2522_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2479_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2479_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v___x_2476_);
lean_dec_ref_known(v___x_2474_, 2);
lean_dec(v___x_2473_);
lean_dec(v___x_2470_);
lean_dec_ref_known(v___x_2467_, 2);
lean_dec(v___x_2450_);
lean_dec_ref_known(v___x_2443_, 4);
lean_dec_ref_known(v___x_2438_, 2);
lean_dec_ref_known(v___x_2435_, 2);
lean_dec(v___x_2433_);
lean_dec_ref(v___x_2429_);
lean_dec_ref_known(v___x_2423_, 2);
lean_dec(v___x_2420_);
lean_dec(v___x_2417_);
lean_dec_ref_known(v___x_2405_, 3);
lean_dec(v_a_2403_);
lean_dec(v___x_2386_);
lean_dec_ref_known(v___x_2384_, 2);
lean_dec_ref_known(v___x_2382_, 3);
lean_dec(v___x_2376_);
lean_dec_ref(v___f_2354_);
v_a_2530_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2477_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2477_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_a_2401_);
lean_dec_ref(v___x_2398_);
lean_dec_ref(v___x_2394_);
lean_dec(v___x_2386_);
lean_dec_ref_known(v___x_2384_, 2);
lean_dec_ref_known(v___x_2382_, 3);
lean_dec(v___x_2376_);
lean_dec_ref(v_str_2366_);
lean_dec_ref(v___x_2356_);
lean_dec_ref(v___x_2355_);
lean_dec_ref(v___f_2354_);
v_a_2538_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2402_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2402_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v___x_2398_);
lean_dec_ref(v___x_2394_);
lean_dec(v___x_2386_);
lean_dec_ref_known(v___x_2384_, 2);
lean_dec_ref_known(v___x_2382_, 3);
lean_dec(v___x_2376_);
lean_dec_ref(v_str_2366_);
lean_dec_ref(v___x_2356_);
lean_dec_ref(v___x_2355_);
lean_dec_ref(v___f_2354_);
v_a_2546_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2400_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2400_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v___x_2394_);
lean_dec(v___x_2386_);
lean_dec_ref_known(v___x_2384_, 2);
lean_dec_ref_known(v___x_2382_, 3);
lean_dec(v___x_2376_);
lean_dec_ref(v_str_2366_);
lean_dec_ref(v___x_2356_);
lean_dec_ref(v___x_2355_);
lean_dec_ref(v___f_2354_);
v_a_2554_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2395_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2395_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v_str_2366_);
lean_dec_ref(v_argVars_2357_);
lean_dec_ref(v___x_2356_);
lean_dec_ref(v___x_2355_);
lean_dec_ref(v___f_2354_);
v_a_2562_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2369_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2369_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref(v_argVars_2357_);
lean_dec_ref(v___x_2356_);
lean_dec_ref(v___x_2355_);
lean_dec_ref(v___f_2354_);
v___x_2570_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___closed__11);
v___x_2571_ = l_Lean_MessageData_ofName(v_v_2353_);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_2572_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___boxed(lean_object* v_v_2574_, lean_object* v___f_2575_, lean_object* v___x_2576_, lean_object* v___x_2577_, lean_object* v_argVars_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1(v_v_2574_, v___f_2575_, v___x_2576_, v___x_2577_, v_argVars_2578_, v_x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_x_2579_);
return v_res_2587_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_instMonadEIO(lean_box(0));
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_toApplicative_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2696_; 
v___x_2603_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__0);
v___x_2604_ = l_StateRefT_x27_instMonad___redArg(v___x_2603_);
v_toApplicative_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2604_, 1);
lean_dec(v_unused_2697_);
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2696_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_toApplicative_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2696_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_toFunctor_2609_; lean_object* v_toSeq_2610_; lean_object* v_toSeqLeft_2611_; lean_object* v_toSeqRight_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2694_; 
v_toFunctor_2609_ = lean_ctor_get(v_toApplicative_2605_, 0);
v_toSeq_2610_ = lean_ctor_get(v_toApplicative_2605_, 2);
v_toSeqLeft_2611_ = lean_ctor_get(v_toApplicative_2605_, 3);
v_toSeqRight_2612_ = lean_ctor_get(v_toApplicative_2605_, 4);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_toApplicative_2605_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v_toApplicative_2605_, 1);
lean_dec(v_unused_2695_);
v___x_2614_ = v_toApplicative_2605_;
v_isShared_2615_ = v_isSharedCheck_2694_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_toSeqRight_2612_);
lean_inc(v_toSeqLeft_2611_);
lean_inc(v_toSeq_2610_);
lean_inc(v_toFunctor_2609_);
lean_dec(v_toApplicative_2605_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2694_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___f_2623_; lean_object* v___x_2625_; 
v___f_2616_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__1));
v___f_2617_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__2));
lean_inc_ref(v_toFunctor_2609_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toFunctor_2609_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toFunctor_2609_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___f_2618_);
lean_ctor_set(v___x_2620_, 1, v___f_2619_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toSeqRight_2612_);
v___f_2622_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2622_, 0, v_toSeqLeft_2611_);
v___f_2623_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2623_, 0, v_toSeq_2610_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 4, v___f_2621_);
lean_ctor_set(v___x_2614_, 3, v___f_2622_);
lean_ctor_set(v___x_2614_, 2, v___f_2623_);
lean_ctor_set(v___x_2614_, 1, v___f_2616_);
lean_ctor_set(v___x_2614_, 0, v___x_2620_);
v___x_2625_ = v___x_2614_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___f_2616_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v___f_2623_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v___f_2622_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v___f_2621_);
v___x_2625_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 1, v___f_2617_);
lean_ctor_set(v___x_2607_, 0, v___x_2625_);
v___x_2627_ = v___x_2607_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___f_2617_);
v___x_2627_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v_toApplicative_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2690_; 
v___x_2628_ = l_StateRefT_x27_instMonad___redArg(v___x_2627_);
v_toApplicative_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v___x_2628_, 1);
lean_dec(v_unused_2691_);
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2690_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_toApplicative_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2690_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_toFunctor_2633_; lean_object* v_toSeq_2634_; lean_object* v_toSeqLeft_2635_; lean_object* v_toSeqRight_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2688_; 
v_toFunctor_2633_ = lean_ctor_get(v_toApplicative_2629_, 0);
v_toSeq_2634_ = lean_ctor_get(v_toApplicative_2629_, 2);
v_toSeqLeft_2635_ = lean_ctor_get(v_toApplicative_2629_, 3);
v_toSeqRight_2636_ = lean_ctor_get(v_toApplicative_2629_, 4);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_toApplicative_2629_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_toApplicative_2629_, 1);
lean_dec(v_unused_2689_);
v___x_2638_ = v_toApplicative_2629_;
v_isShared_2639_ = v_isSharedCheck_2688_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_toSeqRight_2636_);
lean_inc(v_toSeqLeft_2635_);
lean_inc(v_toSeq_2634_);
lean_inc(v_toFunctor_2633_);
lean_dec(v_toApplicative_2629_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2688_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___x_2649_; 
v___f_2640_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__3));
v___f_2641_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__4));
lean_inc_ref(v_toFunctor_2633_);
v___f_2642_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2642_, 0, v_toFunctor_2633_);
v___f_2643_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2643_, 0, v_toFunctor_2633_);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___f_2642_);
lean_ctor_set(v___x_2644_, 1, v___f_2643_);
v___f_2645_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2645_, 0, v_toSeqRight_2636_);
v___f_2646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2646_, 0, v_toSeqLeft_2635_);
v___f_2647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2647_, 0, v_toSeq_2634_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___f_2645_);
lean_ctor_set(v___x_2638_, 3, v___f_2646_);
lean_ctor_set(v___x_2638_, 2, v___f_2647_);
lean_ctor_set(v___x_2638_, 1, v___f_2640_);
lean_ctor_set(v___x_2638_, 0, v___x_2644_);
v___x_2649_ = v___x_2638_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___f_2640_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v___f_2647_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v___f_2646_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v___f_2645_);
v___x_2649_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v___f_2641_);
lean_ctor_set(v___x_2631_, 0, v___x_2649_);
v___x_2651_ = v___x_2631_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___f_2641_);
v___x_2651_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v_toApplicative_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2684_; 
v___x_2652_ = l_StateRefT_x27_instMonad___redArg(v___x_2651_);
v_toApplicative_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; 
v_unused_2685_ = lean_ctor_get(v___x_2652_, 1);
lean_dec(v_unused_2685_);
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2684_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_toApplicative_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2684_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_toFunctor_2657_; lean_object* v_toSeq_2658_; lean_object* v_toSeqLeft_2659_; lean_object* v_toSeqRight_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2682_; 
v_toFunctor_2657_ = lean_ctor_get(v_toApplicative_2653_, 0);
v_toSeq_2658_ = lean_ctor_get(v_toApplicative_2653_, 2);
v_toSeqLeft_2659_ = lean_ctor_get(v_toApplicative_2653_, 3);
v_toSeqRight_2660_ = lean_ctor_get(v_toApplicative_2653_, 4);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_toApplicative_2653_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v_toApplicative_2653_, 1);
lean_dec(v_unused_2683_);
v___x_2662_ = v_toApplicative_2653_;
v_isShared_2663_ = v_isSharedCheck_2682_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_toSeqRight_2660_);
lean_inc(v_toSeqLeft_2659_);
lean_inc(v_toSeq_2658_);
lean_inc(v_toFunctor_2657_);
lean_dec(v_toApplicative_2653_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2682_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___f_2664_; lean_object* v___f_2665_; lean_object* v___f_2666_; lean_object* v___f_2667_; lean_object* v___x_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___x_2673_; 
v___f_2664_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__5));
v___f_2665_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___closed__6));
lean_inc_ref(v_toFunctor_2657_);
v___f_2666_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2666_, 0, v_toFunctor_2657_);
v___f_2667_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2667_, 0, v_toFunctor_2657_);
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___f_2666_);
lean_ctor_set(v___x_2668_, 1, v___f_2667_);
v___f_2669_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2669_, 0, v_toSeqRight_2660_);
v___f_2670_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2670_, 0, v_toSeqLeft_2659_);
v___f_2671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2671_, 0, v_toSeq_2658_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 4, v___f_2669_);
lean_ctor_set(v___x_2662_, 3, v___f_2670_);
lean_ctor_set(v___x_2662_, 2, v___f_2671_);
lean_ctor_set(v___x_2662_, 1, v___f_2664_);
lean_ctor_set(v___x_2662_, 0, v___x_2668_);
v___x_2673_ = v___x_2662_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___f_2664_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v___f_2671_);
lean_ctor_set(v_reuseFailAlloc_2681_, 3, v___f_2670_);
lean_ctor_set(v_reuseFailAlloc_2681_, 4, v___f_2669_);
v___x_2673_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___f_2665_);
lean_ctor_set(v___x_2655_, 0, v___x_2673_);
v___x_2675_ = v___x_2655_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___f_2665_);
v___x_2675_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_39397__overap_2678_; lean_object* v___x_2679_; 
v___x_2676_ = lean_box(0);
v___x_2677_ = l_instInhabitedOfMonad___redArg(v___x_2675_, v___x_2676_);
v___x_39397__overap_2678_ = lean_panic_fn_borrowed(v___x_2677_, v_msg_2595_);
lean_dec(v___x_2677_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
v___x_2679_ = lean_apply_7(v___x_39397__overap_2678_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, lean_box(0));
return v___x_2679_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___boxed(lean_object* v_msg_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(v_msg_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
return v_res_2706_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__0));
v___x_2709_ = l_Lean_stringToMessageData(v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__2));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2716_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__6));
v___x_2717_ = lean_unsigned_to_nat(11u);
v___x_2718_ = lean_unsigned_to_nat(122u);
v___x_2719_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__5));
v___x_2720_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__4));
v___x_2721_ = l_mkPanicMessageWithDecl(v___x_2720_, v___x_2719_, v___x_2718_, v___x_2717_, v___x_2716_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(lean_object* v_constName_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2738_; lean_object* v_env_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2738_ = lean_st_ref_get(v___y_2728_);
v_env_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_ref(v_env_2739_);
lean_dec(v___x_2738_);
v___x_2740_ = 0;
lean_inc(v_constName_2722_);
v___x_2741_ = l_Lean_Environment_findAsync_x3f(v_env_2739_, v_constName_2722_, v___x_2740_);
if (lean_obj_tag(v___x_2741_) == 1)
{
lean_object* v_val_2742_; uint8_t v_kind_2743_; 
v_val_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_val_2742_);
lean_dec_ref_known(v___x_2741_, 1);
v_kind_2743_ = lean_ctor_get_uint8(v_val_2742_, sizeof(void*)*3);
if (v_kind_2743_ == 6)
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2742_);
if (lean_obj_tag(v___x_2744_) == 6)
{
lean_object* v_val_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_constName_2722_);
v_val_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_val_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 0);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_val_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec_ref(v___x_2744_);
v___x_2753_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__7);
v___x_2754_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(v___x_2753_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2763_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2763_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
if (lean_obj_tag(v_a_2755_) == 0)
{
lean_del_object(v___x_2757_);
goto v___jp_2730_;
}
else
{
lean_object* v_val_2759_; lean_object* v___x_2761_; 
lean_dec(v_constName_2722_);
v_val_2759_ = lean_ctor_get(v_a_2755_, 0);
lean_inc(v_val_2759_);
lean_dec_ref_known(v_a_2755_, 1);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v_val_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_val_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_constName_2722_);
v_a_2764_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2754_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2754_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
else
{
lean_dec(v_val_2742_);
goto v___jp_2730_;
}
}
else
{
lean_dec(v___x_2741_);
goto v___jp_2730_;
}
v___jp_2730_:
{
lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2731_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1);
v___x_2732_ = 0;
v___x_2733_ = l_Lean_MessageData_ofConstName(v_constName_2722_, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2731_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__3);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(v___x_2736_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___boxed(lean_object* v_constName_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(v_constName_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(lean_object* v_params_2782_, size_t v_sz_2783_, size_t v_i_2784_, lean_object* v_bs_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v___x_2793_; 
v___x_2793_ = lean_usize_dec_lt(v_i_2784_, v_sz_2783_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_bs_2785_);
return v___x_2794_;
}
else
{
lean_object* v_v_2795_; lean_object* v___x_2796_; 
v_v_2795_ = lean_array_uget_borrowed(v_bs_2785_, v_i_2784_);
lean_inc(v_v_2795_);
v___x_2796_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(v_v_2795_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v_toConstantVal_2798_; lean_object* v_type_2799_; lean_object* v___x_2800_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v_toConstantVal_2798_ = lean_ctor_get(v_a_2797_, 0);
lean_inc_ref(v_toConstantVal_2798_);
lean_dec(v_a_2797_);
v_type_2799_ = lean_ctor_get(v_toConstantVal_2798_, 2);
lean_inc_ref(v_type_2799_);
lean_dec_ref(v_toConstantVal_2798_);
v___x_2800_ = l_Lean_Meta_instantiateForall(v_type_2799_, v_params_2782_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___f_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___f_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___f_2802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___closed__0));
v___x_2803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0));
v___x_2804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1));
lean_inc(v_v_2795_);
v___f_2805_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2805_, 0, v_v_2795_);
lean_closure_set(v___f_2805_, 1, v___f_2802_);
lean_closure_set(v___f_2805_, 2, v___x_2803_);
lean_closure_set(v___f_2805_, 3, v___x_2804_);
v___x_2806_ = 0;
v___x_2807_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___redArg(v_a_2801_, v___f_2805_, v___x_2806_, v___x_2806_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v_bs_x27_2810_; size_t v___x_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_unsigned_to_nat(0u);
v_bs_x27_2810_ = lean_array_uset(v_bs_2785_, v_i_2784_, v___x_2809_);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2784_, v___x_2811_);
v___x_2813_ = lean_array_uset(v_bs_x27_2810_, v_i_2784_, v_a_2808_);
v_i_2784_ = v___x_2812_;
v_bs_2785_ = v___x_2813_;
goto _start;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v_bs_2785_);
v_a_2815_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2807_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2807_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v_bs_2785_);
v_a_2823_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2800_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2800_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v_bs_2785_);
v_a_2831_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2796_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2796_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___boxed(lean_object* v_params_2839_, lean_object* v_sz_2840_, lean_object* v_i_2841_, lean_object* v_bs_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
size_t v_sz_boxed_2850_; size_t v_i_boxed_2851_; lean_object* v_res_2852_; 
v_sz_boxed_2850_ = lean_unbox_usize(v_sz_2840_);
lean_dec(v_sz_2840_);
v_i_boxed_2851_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(v_params_2839_, v_sz_boxed_2850_, v_i_boxed_2851_, v_bs_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v_params_2839_);
return v_res_2852_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0));
v___x_2866_ = l_String_toRawSubstring_x27(v___x_2865_);
return v___x_2866_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7));
v___x_2875_ = l_String_toRawSubstring_x27(v___x_2874_);
return v___x_2875_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19));
v___x_2905_ = l_String_toRawSubstring_x27(v___x_2904_);
return v___x_2905_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24));
v___x_2913_ = l_String_toRawSubstring_x27(v___x_2912_);
return v___x_2913_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30));
v___x_2925_ = l_Lean_stringToMessageData(v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(lean_object* v_indVal_2926_, lean_object* v_params_2927_, lean_object* v_encInstBinders_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_options_2936_; lean_object* v_toCold_2937_; uint8_t v_hasTrace_2938_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; 
v_options_2936_ = lean_ctor_get(v_a_2933_, 1);
v_toCold_2937_ = lean_ctor_get(v_a_2933_, 0);
v_hasTrace_2938_ = lean_ctor_get_uint8(v_options_2936_, sizeof(void*)*1);
if (v_hasTrace_2938_ == 0)
{
v___y_2940_ = v_a_2929_;
v___y_2941_ = v_a_2930_;
v___y_2942_ = v_a_2931_;
v___y_2943_ = v_a_2932_;
v___y_2944_ = v_a_2933_;
v___y_2945_ = v_a_2934_;
goto v___jp_2939_;
}
else
{
lean_object* v_inheritedTraceOptions_3266_; lean_object* v_cls_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v_inheritedTraceOptions_3266_ = lean_ctor_get(v_toCold_2937_, 4);
v_cls_3267_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135));
v___x_3268_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138);
v___x_3269_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3266_, v_options_2936_, v___x_3268_);
if (v___x_3269_ == 0)
{
v___y_2940_ = v_a_2929_;
v___y_2941_ = v_a_2930_;
v___y_2942_ = v_a_2931_;
v___y_2943_ = v_a_2932_;
v___y_2944_ = v_a_2933_;
v___y_2945_ = v_a_2934_;
goto v___jp_2939_;
}
else
{
lean_object* v_toConstantVal_3270_; lean_object* v_name_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_toConstantVal_3270_ = lean_ctor_get(v_indVal_2926_, 0);
v_name_3271_ = lean_ctor_get(v_toConstantVal_3270_, 0);
v___x_3272_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31);
lean_inc(v_name_3271_);
v___x_3273_ = l_Lean_MessageData_ofName(v_name_3271_);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__142);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
lean_inc_ref(v_params_2927_);
v___x_3277_ = lean_array_to_list(v_params_2927_);
v___x_3278_ = lean_box(0);
v___x_3279_ = l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(v___x_3277_, v___x_3278_);
v___x_3280_ = l_Lean_MessageData_ofList(v___x_3279_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3276_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(v_cls_3267_, v___x_3281_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_dec_ref_known(v___x_3282_, 1);
v___y_2940_ = v_a_2929_;
v___y_2941_ = v_a_2930_;
v___y_2942_ = v_a_2931_;
v___y_2943_ = v_a_2932_;
v___y_2944_ = v_a_2933_;
v___y_2945_ = v_a_2934_;
goto v___jp_2939_;
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_params_2927_);
lean_dec_ref(v_indVal_2926_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
v___jp_2939_:
{
lean_object* v_toConstantVal_2946_; lean_object* v_ctors_2947_; lean_object* v___x_2948_; size_t v_sz_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v_toConstantVal_2946_ = lean_ctor_get(v_indVal_2926_, 0);
lean_inc_ref(v_toConstantVal_2946_);
v_ctors_2947_ = lean_ctor_get(v_indVal_2926_, 4);
lean_inc(v_ctors_2947_);
lean_dec_ref(v_indVal_2926_);
v___x_2948_ = lean_array_mk(v_ctors_2947_);
v_sz_2949_ = lean_array_size(v___x_2948_);
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(v_params_2927_, v_sz_2949_, v___x_2950_, v___x_2948_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v_fst_2954_; lean_object* v_snd_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3257_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l_Array_unzip___redArg(v_a_2952_);
lean_dec(v_a_2952_);
v_fst_2954_ = lean_ctor_get(v___x_2953_, 0);
v_snd_2955_ = lean_ctor_get(v___x_2953_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_2957_ = v___x_2953_;
v_isShared_2958_ = v_isSharedCheck_3257_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_snd_2955_);
lean_inc(v_fst_2954_);
lean_dec(v___x_2953_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3257_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v_fst_2960_; lean_object* v_snd_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3256_; 
v___x_2959_ = l_Array_unzip___redArg(v_snd_2955_);
lean_dec(v_snd_2955_);
v_fst_2960_ = lean_ctor_get(v___x_2959_, 0);
v_snd_2961_ = lean_ctor_get(v___x_2959_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_3256_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snd_2961_);
lean_inc(v_fst_2960_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3256_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
size_t v_sz_2965_; lean_object* v___x_2966_; 
v_sz_2965_ = lean_array_size(v_params_2927_);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(v_sz_2965_, v___x_2950_, v_params_2927_, v___y_2942_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_toCold_2967_; lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3247_; 
v_toCold_2967_ = lean_ctor_get(v___y_2944_, 0);
v_a_2968_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_2970_ = v___x_2966_;
v_isShared_2971_ = v_isSharedCheck_3247_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3247_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v_ref_2972_; lean_object* v_currMacroScope_2973_; lean_object* v_name_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3244_; 
v_ref_2972_ = lean_ctor_get(v___y_2944_, 4);
v_currMacroScope_2973_ = lean_ctor_get(v___y_2944_, 9);
v_name_2974_ = lean_ctor_get(v_toConstantVal_2946_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_toConstantVal_2946_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; lean_object* v_unused_3246_; 
v_unused_3245_ = lean_ctor_get(v_toConstantVal_2946_, 2);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_toConstantVal_2946_, 1);
lean_dec(v_unused_3246_);
v___x_2976_ = v_toConstantVal_2946_;
v_isShared_2977_ = v_isSharedCheck_3244_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_name_2974_);
lean_dec(v_toConstantVal_2946_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3244_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v_quotContext_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v_quotContext_2978_ = lean_ctor_get(v_toCold_2967_, 2);
v___x_2979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_2980_ = 0;
v___x_2981_ = l_Lean_SourceInfo_fromRef(v_ref_2972_, v___x_2980_);
v___x_2982_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66));
lean_inc(v___x_2981_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 2);
lean_ctor_set(v___x_2963_, 1, v___x_2982_);
lean_ctor_set(v___x_2963_, 0, v___x_2981_);
v___x_2984_ = v___x_2963_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_3243_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; size_t v_sz_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2985_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65));
v___x_2986_ = l_Lean_mkCIdent(v_name_2974_);
lean_inc_n(v___x_2981_, 2);
v___x_2987_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2985_, v___x_2984_, v___x_2986_);
v_sz_2988_ = lean_array_size(v_a_2968_);
v___x_2989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_2990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(v_sz_2988_, v___x_2950_, v_a_2968_);
v___x_2992_ = l_Array_append___redArg(v___x_2990_, v___x_2991_);
lean_dec_ref(v___x_2991_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set_tag(v___x_2976_, 1);
lean_ctor_set(v___x_2976_, 2, v___x_2992_);
lean_ctor_set(v___x_2976_, 1, v___x_2989_);
lean_ctor_set(v___x_2976_, 0, v___x_2981_);
v___x_2994_ = v___x_2976_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_3242_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
lean_inc_n(v___x_2981_, 4);
v___x_2995_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2979_, v___x_2987_, v___x_2994_);
v___x_2996_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5));
v___x_2997_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
v___x_2998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2981_);
lean_ctor_set(v___x_2998_, 1, v___x_2989_);
lean_ctor_set(v___x_2998_, 2, v___x_2990_);
lean_inc_ref_n(v___x_2998_, 7);
v___x_2999_ = l_Lean_Syntax_node7(v___x_2981_, v___x_2997_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_);
v___x_3000_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0));
v___x_3001_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1));
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 2);
lean_ctor_set(v___x_2957_, 1, v___x_3000_);
lean_ctor_set(v___x_2957_, 0, v___x_2981_);
v___x_3003_ = v___x_2957_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3000_);
v___x_3003_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; size_t v_sz_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; size_t v_sz_3154_; lean_object* v___x_3155_; size_t v_sz_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; size_t v_sz_3213_; lean_object* v___x_3214_; size_t v_sz_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3004_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13));
v___x_3005_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15);
v___x_3006_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
lean_inc_n(v_currMacroScope_2973_, 14);
lean_inc_n(v_quotContext_2978_, 14);
v___x_3007_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3006_, v_currMacroScope_2973_);
v___x_3008_ = lean_box(0);
lean_inc_n(v___x_2981_, 114);
v___x_3009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3009_, 0, v___x_2981_);
lean_ctor_set(v___x_3009_, 1, v___x_3005_);
lean_ctor_set(v___x_3009_, 2, v___x_3007_);
lean_ctor_set(v___x_3009_, 3, v___x_3008_);
lean_inc_ref_n(v___x_2998_, 50);
lean_inc_ref(v___x_3009_);
v___x_3010_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3004_, v___x_3009_, v___x_2998_);
v___x_3011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
v___x_3012_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3011_, v___x_2998_, v___x_2998_);
v___x_3013_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17));
v___x_3014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_2981_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
lean_inc_ref(v___x_3014_);
v___x_3015_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3014_);
v_sz_3016_ = lean_array_size(v_fst_2954_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_3016_, v___x_2950_, v_fst_2954_);
v___x_3018_ = l_Array_append___redArg(v___x_2990_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3019_, 0, v___x_2981_);
lean_ctor_set(v___x_3019_, 1, v___x_2989_);
lean_ctor_set(v___x_3019_, 2, v___x_3018_);
v___x_3020_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21));
v___x_3021_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22));
v___x_3022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_2981_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24));
v___x_3024_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26);
v___x_3025_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27));
v___x_3026_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3025_, v_currMacroScope_2973_);
v___x_3027_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32));
v___x_3028_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3028_, 0, v___x_2981_);
lean_ctor_set(v___x_3028_, 1, v___x_3024_);
lean_ctor_set(v___x_3028_, 2, v___x_3026_);
lean_ctor_set(v___x_3028_, 3, v___x_3027_);
v___x_3029_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3023_, v___x_2998_, v___x_3028_);
v___x_3030_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33));
v___x_3031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_2981_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35);
v___x_3033_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36));
v___x_3034_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3033_, v_currMacroScope_2973_);
v___x_3035_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41));
v___x_3036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3036_, 0, v___x_2981_);
lean_ctor_set(v___x_3036_, 1, v___x_3032_);
lean_ctor_set(v___x_3036_, 2, v___x_3034_);
lean_ctor_set(v___x_3036_, 3, v___x_3035_);
v___x_3037_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3023_, v___x_2998_, v___x_3036_);
lean_inc_ref(v___x_3031_);
v___x_3038_ = l_Lean_Syntax_node3(v___x_2981_, v___x_2989_, v___x_3029_, v___x_3031_, v___x_3037_);
v___x_3039_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2989_, v___x_3022_, v___x_3038_);
v___x_3040_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3020_, v___x_3039_);
v___x_3041_ = l_Lean_Syntax_node8(v___x_2981_, v___x_3001_, v___x_3003_, v___x_3010_, v___x_3012_, v___x_3015_, v___x_3019_, v___x_2998_, v___x_3040_, v___x_2998_);
v___x_3042_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2996_, v___x_2999_, v___x_3041_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42));
v___x_3044_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43));
v___x_3045_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44));
v___x_3046_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45));
v___x_3047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_2981_);
lean_ctor_set(v___x_3047_, 1, v___x_3045_);
v___x_3048_ = l_Array_append___redArg(v___x_2990_, v_encInstBinders_2928_);
v___x_3049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_2981_);
lean_ctor_set(v___x_3049_, 1, v___x_2989_);
lean_ctor_set(v___x_3049_, 2, v___x_3048_);
v___x_3050_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3046_, v___x_3047_, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_2981_);
lean_ctor_set(v___x_3051_, 1, v___x_3043_);
v___x_3052_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2));
v___x_3053_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3));
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_2981_);
lean_ctor_set(v___x_3054_, 1, v___x_3052_);
v___x_3055_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3053_, v___x_3054_);
v___x_3056_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3055_);
v___x_3057_ = l_Lean_Syntax_node7(v___x_2981_, v___x_2997_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_2998_, v___x_3056_);
v___x_3058_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46));
v___x_3059_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47));
v___x_3060_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49));
v___x_3061_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3060_, v___x_2998_);
v___x_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_2981_);
lean_ctor_set(v___x_3062_, 1, v___x_3058_);
v___x_3063_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51));
v___x_3064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
v___x_3065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_2981_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52);
v___x_3068_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
v___x_3069_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3068_, v_currMacroScope_2973_);
v___x_3070_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56));
v___x_3071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3071_, 0, v___x_2981_);
lean_ctor_set(v___x_3071_, 1, v___x_3067_);
lean_ctor_set(v___x_3071_, 2, v___x_3069_);
lean_ctor_set(v___x_3071_, 3, v___x_3070_);
v___x_3072_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_2995_);
v___x_3073_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2979_, v___x_3071_, v___x_3072_);
lean_inc_ref(v___x_3066_);
v___x_3074_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3064_, v___x_3066_, v___x_3073_);
lean_inc(v___x_3074_);
v___x_3075_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3063_, v___x_2998_, v___x_3074_);
v___x_3076_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68));
v___x_3077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14));
v___x_3078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_2981_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70));
v___x_3080_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71));
v___x_3081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_2981_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73));
v___x_3083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8));
v___x_3084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10));
v___x_3085_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23);
v___x_3086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24));
v___x_3087_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3086_, v_currMacroScope_2973_);
v___x_3088_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75));
v___x_3089_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3089_, 0, v___x_2981_);
lean_ctor_set(v___x_3089_, 1, v___x_3085_);
lean_ctor_set(v___x_3089_, 2, v___x_3087_);
lean_ctor_set(v___x_3089_, 3, v___x_3088_);
v___x_3090_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3084_, v___x_3089_, v___x_2998_);
v___x_3091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
v___x_3092_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77);
v___x_3093_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78));
v___x_3094_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3093_, v_currMacroScope_2973_);
v___x_3095_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3095_, 0, v___x_2981_);
lean_ctor_set(v___x_3095_, 1, v___x_3092_);
lean_ctor_set(v___x_3095_, 2, v___x_3094_);
lean_ctor_set(v___x_3095_, 3, v___x_3008_);
lean_inc_ref(v___x_3095_);
lean_inc_ref_n(v___x_3078_, 5);
v___x_3096_ = l_Lean_Syntax_node3(v___x_2981_, v___x_3091_, v___x_3078_, v___x_2998_, v___x_3095_);
v___x_3097_ = l_Lean_Syntax_node3(v___x_2981_, v___x_2989_, v___x_2998_, v___x_2998_, v___x_3096_);
v___x_3098_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3083_, v___x_3090_, v___x_3097_);
v___x_3099_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39);
v___x_3100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
v___x_3101_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3100_, v_currMacroScope_2973_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80));
v___x_3103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3103_, 0, v___x_2981_);
lean_ctor_set(v___x_3103_, 1, v___x_3099_);
lean_ctor_set(v___x_3103_, 2, v___x_3101_);
lean_ctor_set(v___x_3103_, 3, v___x_3102_);
v___x_3104_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3084_, v___x_3103_, v___x_2998_);
v___x_3105_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82);
v___x_3106_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83));
v___x_3107_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3106_, v_currMacroScope_2973_);
v___x_3108_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3108_, 0, v___x_2981_);
lean_ctor_set(v___x_3108_, 1, v___x_3105_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
lean_ctor_set(v___x_3108_, 3, v___x_3008_);
lean_inc_ref(v___x_3108_);
v___x_3109_ = l_Lean_Syntax_node3(v___x_2981_, v___x_3091_, v___x_3078_, v___x_2998_, v___x_3108_);
v___x_3110_ = l_Lean_Syntax_node3(v___x_2981_, v___x_2989_, v___x_2998_, v___x_2998_, v___x_3109_);
v___x_3111_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3083_, v___x_3104_, v___x_3110_);
v___x_3112_ = l_Lean_Syntax_node3(v___x_2981_, v___x_2989_, v___x_3098_, v___x_3031_, v___x_3111_);
v___x_3113_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3082_, v___x_3112_);
v___x_3114_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85));
v___x_3115_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3114_, v___x_2998_);
v___x_3116_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86));
v___x_3117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_2981_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_Syntax_node6(v___x_2981_, v___x_3079_, v___x_3081_, v___x_2998_, v___x_3113_, v___x_3115_, v___x_2998_, v___x_3117_);
v___x_3119_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89));
v___x_3120_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3119_, v___x_2998_, v___x_2998_);
v___x_3121_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91));
v___x_3122_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93));
v___x_3123_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95));
v___x_3124_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97));
v___x_3125_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99));
v___x_3126_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3125_, v___x_3095_);
v___x_3127_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4);
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1));
v___x_3129_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3128_, v_currMacroScope_2973_);
v___x_3130_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3130_, 0, v___x_2981_);
lean_ctor_set(v___x_3130_, 1, v___x_3127_);
lean_ctor_set(v___x_3130_, 2, v___x_3129_);
lean_ctor_set(v___x_3130_, 3, v___x_3008_);
lean_inc_ref(v___x_3130_);
v___x_3131_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3130_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5));
v___x_3133_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6));
v___x_3134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_2981_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
v___x_3135_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123));
v___x_3136_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3135_, v___x_2998_);
v___x_3137_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8);
v___x_3138_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9));
v___x_3139_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3138_, v_currMacroScope_2973_);
v___x_3140_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3140_, 0, v___x_2981_);
lean_ctor_set(v___x_3140_, 1, v___x_3137_);
lean_ctor_set(v___x_3140_, 2, v___x_3139_);
lean_ctor_set(v___x_3140_, 3, v___x_3008_);
v___x_3141_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3125_, v___x_3140_);
v___x_3142_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3074_);
lean_inc(v___x_3118_);
v___x_3143_ = l_Lean_Syntax_node5(v___x_2981_, v___x_3124_, v___x_3141_, v___x_2998_, v___x_3142_, v___x_3078_, v___x_3118_);
v___x_3144_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3123_, v___x_3143_);
v___x_3145_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10));
v___x_3146_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11));
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_2981_);
lean_ctor_set(v___x_3147_, 1, v___x_3145_);
v___x_3148_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13));
v___x_3149_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3148_, v___x_2998_, v___x_3130_);
v___x_3150_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3149_);
v___x_3151_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14));
v___x_3152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_2981_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16));
v_sz_3154_ = lean_array_size(v_fst_2960_);
v___x_3155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(v_sz_3154_, v___x_2950_, v_fst_2960_);
v_sz_3156_ = lean_array_size(v___x_3155_);
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_3156_, v___x_2950_, v___x_3155_);
v___x_3158_ = l_Array_append___redArg(v___x_2990_, v___x_3157_);
lean_dec_ref(v___x_3157_);
v___x_3159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3159_, 0, v___x_2981_);
lean_ctor_set(v___x_3159_, 1, v___x_2989_);
lean_ctor_set(v___x_3159_, 2, v___x_3158_);
v___x_3160_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3153_, v___x_3159_);
lean_inc_ref(v___x_3152_);
lean_inc_ref(v___x_3147_);
v___x_3161_ = l_Lean_Syntax_node6(v___x_2981_, v___x_3146_, v___x_3147_, v___x_2998_, v___x_2998_, v___x_3150_, v___x_3152_, v___x_3160_);
lean_inc(v___x_3144_);
lean_inc_n(v___x_3136_, 2);
lean_inc_ref(v___x_3134_);
v___x_3162_ = l_Lean_Syntax_node5(v___x_2981_, v___x_3133_, v___x_3134_, v___x_3136_, v___x_3144_, v___x_2998_, v___x_3161_);
v___x_3163_ = l_Lean_Syntax_node5(v___x_2981_, v___x_3124_, v___x_3126_, v___x_3131_, v___x_2998_, v___x_3078_, v___x_3162_);
v___x_3164_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3123_, v___x_3163_);
lean_inc_n(v___x_3120_, 2);
v___x_3165_ = l_Lean_Syntax_node4(v___x_2981_, v___x_3122_, v___x_2998_, v___x_2998_, v___x_3164_, v___x_3120_);
v___x_3166_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3125_, v___x_3108_);
v___x_3167_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111);
v___x_3168_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112));
v___x_3169_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3168_, v_currMacroScope_2973_);
v___x_3170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3170_, 0, v___x_2981_);
lean_ctor_set(v___x_3170_, 1, v___x_3167_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
lean_ctor_set(v___x_3170_, 3, v___x_3008_);
v___x_3171_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3170_);
v___x_3172_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113));
v___x_3173_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114));
v___x_3174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_2981_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
v___x_3175_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116));
v___x_3176_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118));
v___x_3177_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18));
v___x_3178_ = l_Lean_Syntax_node3(v___x_2981_, v___x_3177_, v___x_3134_, v___x_3136_, v___x_3144_);
v___x_3179_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3176_, v___x_3178_, v___x_2998_);
v___x_3180_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120));
v___x_3181_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121));
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_2981_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125));
v___x_3184_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20);
v___x_3185_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21));
v___x_3186_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3185_, v_currMacroScope_2973_);
v___x_3187_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3187_, 0, v___x_2981_);
lean_ctor_set(v___x_3187_, 1, v___x_3184_);
lean_ctor_set(v___x_3187_, 2, v___x_3186_);
lean_ctor_set(v___x_3187_, 3, v___x_3008_);
v___x_3188_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3064_, v___x_3066_, v___x_3009_);
v___x_3189_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3188_);
v___x_3190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17));
v___x_3191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_2981_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
v___x_3193_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127);
v___x_3194_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128));
v___x_3195_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3194_, v_currMacroScope_2973_);
v___x_3196_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131));
v___x_3197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3197_, 0, v___x_2981_);
lean_ctor_set(v___x_3197_, 1, v___x_3193_);
lean_ctor_set(v___x_3197_, 2, v___x_3195_);
lean_ctor_set(v___x_3197_, 3, v___x_3196_);
lean_inc(v___x_3171_);
v___x_3198_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2979_, v___x_3197_, v___x_3171_);
v___x_3199_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3192_, v___x_3198_);
lean_inc_ref(v___x_3187_);
v___x_3200_ = l_Lean_Syntax_node4(v___x_2981_, v___x_3183_, v___x_3187_, v___x_3189_, v___x_3191_, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_node4(v___x_2981_, v___x_3180_, v___x_3182_, v___x_2998_, v___x_3136_, v___x_3200_);
v___x_3202_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3176_, v___x_3201_, v___x_2998_);
v___x_3203_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23));
v___x_3204_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25);
v___x_3205_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26));
v___x_3206_ = l_Lean_addMacroScope(v_quotContext_2978_, v___x_3205_, v_currMacroScope_2973_);
v___x_3207_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28));
v___x_3208_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3208_, 0, v___x_2981_);
lean_ctor_set(v___x_3208_, 1, v___x_3204_);
lean_ctor_set(v___x_3208_, 2, v___x_3206_);
lean_ctor_set(v___x_3208_, 3, v___x_3207_);
v___x_3209_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29));
v___x_3210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_2981_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3148_, v___x_2998_, v___x_3187_);
v___x_3212_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3211_);
v_sz_3213_ = lean_array_size(v_snd_2961_);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(v_sz_3213_, v___x_2950_, v_snd_2961_);
v_sz_3215_ = lean_array_size(v___x_3214_);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(v_sz_3215_, v___x_2950_, v___x_3214_);
v___x_3217_ = l_Array_append___redArg(v___x_2990_, v___x_3216_);
lean_dec_ref(v___x_3216_);
v___x_3218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3218_, 0, v___x_2981_);
lean_ctor_set(v___x_3218_, 1, v___x_2989_);
lean_ctor_set(v___x_3218_, 2, v___x_3217_);
v___x_3219_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3153_, v___x_3218_);
v___x_3220_ = l_Lean_Syntax_node6(v___x_2981_, v___x_3146_, v___x_3147_, v___x_2998_, v___x_2998_, v___x_3212_, v___x_3152_, v___x_3219_);
v___x_3221_ = l_Lean_Syntax_node3(v___x_2981_, v___x_3203_, v___x_3208_, v___x_3210_, v___x_3220_);
v___x_3222_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3192_, v___x_3221_);
v___x_3223_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3176_, v___x_3222_, v___x_2998_);
v___x_3224_ = l_Lean_Syntax_node3(v___x_2981_, v___x_2989_, v___x_3179_, v___x_3202_, v___x_3223_);
v___x_3225_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3175_, v___x_3224_);
v___x_3226_ = l_Lean_Syntax_node2(v___x_2981_, v___x_3173_, v___x_3174_, v___x_3225_);
v___x_3227_ = l_Lean_Syntax_node5(v___x_2981_, v___x_3124_, v___x_3166_, v___x_3171_, v___x_2998_, v___x_3078_, v___x_3226_);
v___x_3228_ = l_Lean_Syntax_node1(v___x_2981_, v___x_3123_, v___x_3227_);
v___x_3229_ = l_Lean_Syntax_node4(v___x_2981_, v___x_3122_, v___x_2998_, v___x_2998_, v___x_3228_, v___x_3120_);
v___x_3230_ = l_Lean_Syntax_node3(v___x_2981_, v___x_2989_, v___x_3165_, v___x_2998_, v___x_3229_);
v___x_3231_ = l_Lean_Syntax_node3(v___x_2981_, v___x_3121_, v___x_3014_, v___x_3230_, v___x_2998_);
v___x_3232_ = l_Lean_Syntax_node1(v___x_2981_, v___x_2989_, v___x_3231_);
v___x_3233_ = l_Lean_Syntax_node4(v___x_2981_, v___x_3076_, v___x_3078_, v___x_3118_, v___x_3120_, v___x_3232_);
v___x_3234_ = l_Lean_Syntax_node6(v___x_2981_, v___x_3059_, v___x_3061_, v___x_3062_, v___x_2998_, v___x_2998_, v___x_3075_, v___x_3233_);
v___x_3235_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2996_, v___x_3057_, v___x_3234_);
v___x_3236_ = l_Lean_Syntax_node3(v___x_2981_, v___x_3044_, v___x_3050_, v___x_3051_, v___x_3235_);
v___x_3237_ = l_Lean_Syntax_node2(v___x_2981_, v___x_2989_, v___x_3042_, v___x_3236_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_3237_);
v___x_3239_ = v___x_2970_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_del_object(v___x_2963_);
lean_dec(v_snd_2961_);
lean_dec(v_fst_2960_);
lean_del_object(v___x_2957_);
lean_dec(v_fst_2954_);
lean_dec_ref(v_toConstantVal_2946_);
v_a_3248_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_2966_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_2966_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_toConstantVal_2946_);
lean_dec_ref(v_params_2927_);
v_a_3258_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_2951_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_2951_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___boxed(lean_object* v_indVal_3291_, lean_object* v_params_3292_, lean_object* v_encInstBinders_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(v_indVal_3291_, v_params_3292_, v_encInstBinders_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_encInstBinders_3293_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(size_t v_sz_3302_, size_t v_i_3303_, lean_object* v_bs_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(v_sz_3302_, v_i_3303_, v_bs_3304_, v___y_3309_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___boxed(lean_object* v_sz_3313_, lean_object* v_i_3314_, lean_object* v_bs_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
size_t v_sz_boxed_3323_; size_t v_i_boxed_3324_; lean_object* v_res_3325_; 
v_sz_boxed_3323_ = lean_unbox_usize(v_sz_3313_);
lean_dec(v_sz_3313_);
v_i_boxed_3324_ = lean_unbox_usize(v_i_3314_);
lean_dec(v_i_3314_);
v_res_3325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(v_sz_boxed_3323_, v_i_boxed_3324_, v_bs_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(size_t v_sz_3326_, size_t v_i_3327_, lean_object* v_bs_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(v_sz_3326_, v_i_3327_, v_bs_3328_, v___y_3333_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___boxed(lean_object* v_sz_3337_, lean_object* v_i_3338_, lean_object* v_bs_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
size_t v_sz_boxed_3347_; size_t v_i_boxed_3348_; lean_object* v_res_3349_; 
v_sz_boxed_3347_ = lean_unbox_usize(v_sz_3337_);
lean_dec(v_sz_3337_);
v_i_boxed_3348_ = lean_unbox_usize(v_i_3338_);
lean_dec(v_i_3338_);
v_res_3349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(v_sz_boxed_3347_, v_i_boxed_3348_, v_bs_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(size_t v_sz_3350_, size_t v_i_3351_, lean_object* v_bs_3352_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
if (v___x_3353_ == 0)
{
return v_bs_3352_;
}
else
{
lean_object* v_v_3354_; lean_object* v___x_3355_; lean_object* v_bs_x27_3356_; size_t v___x_3357_; size_t v___x_3358_; lean_object* v___x_3359_; 
v_v_3354_ = lean_array_uget(v_bs_3352_, v_i_3351_);
v___x_3355_ = lean_unsigned_to_nat(0u);
v_bs_x27_3356_ = lean_array_uset(v_bs_3352_, v_i_3351_, v___x_3355_);
v___x_3357_ = ((size_t)1ULL);
v___x_3358_ = lean_usize_add(v_i_3351_, v___x_3357_);
v___x_3359_ = lean_array_uset(v_bs_x27_3356_, v_i_3351_, v_v_3354_);
v_i_3351_ = v___x_3358_;
v_bs_3352_ = v___x_3359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2___boxed(lean_object* v_sz_3361_, lean_object* v_i_3362_, lean_object* v_bs_3363_){
_start:
{
size_t v_sz_boxed_3364_; size_t v_i_boxed_3365_; lean_object* v_res_3366_; 
v_sz_boxed_3364_ = lean_unbox_usize(v_sz_3361_);
lean_dec(v_sz_3361_);
v_i_boxed_3365_ = lean_unbox_usize(v_i_3362_);
lean_dec(v_i_3362_);
v_res_3366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(v_sz_boxed_3364_, v_i_boxed_3365_, v_bs_3363_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(lean_object* v_as_3367_, size_t v_i_3368_, size_t v_stop_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_usize_dec_eq(v_i_3368_, v_stop_3369_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_array_uget_borrowed(v_as_3367_, v_i_3368_);
lean_inc(v___x_3377_);
v___x_3378_ = l_Lean_Meta_isType(v___x_3377_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v_a_3381_; uint8_t v___x_3385_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3385_ = lean_unbox(v_a_3379_);
lean_dec(v_a_3379_);
if (v___x_3385_ == 0)
{
v_a_3381_ = v_b_3370_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3386_; 
lean_inc(v___x_3377_);
v___x_3386_ = lean_array_push(v_b_3370_, v___x_3377_);
v_a_3381_ = v___x_3386_;
goto v___jp_3380_;
}
v___jp_3380_:
{
size_t v___x_3382_; size_t v___x_3383_; 
v___x_3382_ = ((size_t)1ULL);
v___x_3383_ = lean_usize_add(v_i_3368_, v___x_3382_);
v_i_3368_ = v___x_3383_;
v_b_3370_ = v_a_3381_;
goto _start;
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_b_3370_);
v_a_3387_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3378_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3378_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v_b_3370_);
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg___boxed(lean_object* v_as_3396_, lean_object* v_i_3397_, lean_object* v_stop_3398_, lean_object* v_b_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
size_t v_i_boxed_3405_; size_t v_stop_boxed_3406_; lean_object* v_res_3407_; 
v_i_boxed_3405_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_stop_boxed_3406_ = lean_unbox_usize(v_stop_3398_);
lean_dec(v_stop_3398_);
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_as_3396_, v_i_boxed_3405_, v_stop_boxed_3406_, v_b_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_as_3396_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(size_t v_sz_3425_, size_t v_i_3426_, lean_object* v_bs_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_usize_dec_lt(v_i_3426_, v_sz_3425_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_bs_3427_);
return v___x_3433_;
}
else
{
lean_object* v_v_3434_; lean_object* v___x_3435_; 
v_v_3434_ = lean_array_uget_borrowed(v_bs_3427_, v_i_3426_);
v___x_3435_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_v_3434_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_toCold_3436_; lean_object* v_a_3437_; lean_object* v_ref_3438_; lean_object* v_currMacroScope_3439_; lean_object* v_quotContext_3440_; lean_object* v___x_3441_; lean_object* v_bs_x27_3442_; uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v_toCold_3436_ = lean_ctor_get(v___y_3429_, 0);
v_a_3437_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3435_, 1);
v_ref_3438_ = lean_ctor_get(v___y_3429_, 4);
v_currMacroScope_3439_ = lean_ctor_get(v___y_3429_, 9);
v_quotContext_3440_ = lean_ctor_get(v_toCold_3436_, 2);
v___x_3441_ = lean_unsigned_to_nat(0u);
v_bs_x27_3442_ = lean_array_uset(v_bs_3427_, v_i_3426_, v___x_3441_);
v___x_3443_ = 0;
v___x_3444_ = l_Lean_SourceInfo_fromRef(v_ref_3438_, v___x_3443_);
v___x_3445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1));
v___x_3446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2));
lean_inc_n(v___x_3444_, 6);
v___x_3447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3444_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
v___x_3449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11);
v___x_3450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3444_);
lean_ctor_set(v___x_3450_, 1, v___x_3448_);
lean_ctor_set(v___x_3450_, 2, v___x_3449_);
v___x_3451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
v___x_3452_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52);
v___x_3453_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
lean_inc(v_currMacroScope_3439_);
lean_inc(v_quotContext_3440_);
v___x_3454_ = l_Lean_addMacroScope(v_quotContext_3440_, v___x_3453_, v_currMacroScope_3439_);
v___x_3455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5));
v___x_3456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3444_);
lean_ctor_set(v___x_3456_, 1, v___x_3452_);
lean_ctor_set(v___x_3456_, 2, v___x_3454_);
lean_ctor_set(v___x_3456_, 3, v___x_3455_);
v___x_3457_ = l_Lean_LocalDecl_userName(v_a_3437_);
lean_dec(v_a_3437_);
v___x_3458_ = l_Lean_mkIdent(v___x_3457_);
v___x_3459_ = l_Lean_Syntax_node1(v___x_3444_, v___x_3448_, v___x_3458_);
v___x_3460_ = l_Lean_Syntax_node2(v___x_3444_, v___x_3451_, v___x_3456_, v___x_3459_);
v___x_3461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6));
v___x_3462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3444_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_Syntax_node4(v___x_3444_, v___x_3445_, v___x_3447_, v___x_3450_, v___x_3460_, v___x_3462_);
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3426_, v___x_3464_);
v___x_3466_ = lean_array_uset(v_bs_x27_3442_, v_i_3426_, v___x_3463_);
v_i_3426_ = v___x_3465_;
v_bs_3427_ = v___x_3466_;
goto _start;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v_bs_3427_);
v_a_3468_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3435_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3435_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___boxed(lean_object* v_sz_3476_, lean_object* v_i_3477_, lean_object* v_bs_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
size_t v_sz_boxed_3483_; size_t v_i_boxed_3484_; lean_object* v_res_3485_; 
v_sz_boxed_3483_ = lean_unbox_usize(v_sz_3476_);
lean_dec(v_sz_3476_);
v_i_boxed_3484_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(v_sz_boxed_3483_, v_i_boxed_3484_, v_bs_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v___y_3479_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(lean_object* v___x_3486_, lean_object* v_a_3487_, lean_object* v___x_3488_, lean_object* v_params_3489_, lean_object* v_x_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_a_3499_; lean_object* v___y_3522_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3532_ = lean_array_get_size(v_params_3489_);
v___x_3533_ = lean_mk_empty_array_with_capacity(v___x_3488_);
v___x_3534_ = lean_nat_dec_lt(v___x_3488_, v___x_3532_);
if (v___x_3534_ == 0)
{
v_a_3499_ = v___x_3533_;
goto v___jp_3498_;
}
else
{
uint8_t v___x_3535_; 
v___x_3535_ = lean_nat_dec_le(v___x_3532_, v___x_3532_);
if (v___x_3535_ == 0)
{
if (v___x_3534_ == 0)
{
v_a_3499_ = v___x_3533_;
goto v___jp_3498_;
}
else
{
size_t v___x_3536_; size_t v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = ((size_t)0ULL);
v___x_3537_ = lean_usize_of_nat(v___x_3532_);
v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_params_3489_, v___x_3536_, v___x_3537_, v___x_3533_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
v___y_3522_ = v___x_3538_;
goto v___jp_3521_;
}
}
else
{
size_t v___x_3539_; size_t v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = ((size_t)0ULL);
v___x_3540_ = lean_usize_of_nat(v___x_3532_);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_params_3489_, v___x_3539_, v___x_3540_, v___x_3533_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
v___y_3522_ = v___x_3541_;
goto v___jp_3521_;
}
}
v___jp_3498_:
{
size_t v_sz_3500_; size_t v___x_3501_; lean_object* v___x_3502_; 
v_sz_3500_ = lean_array_size(v_a_3499_);
v___x_3501_ = ((size_t)0ULL);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(v_sz_3500_, v___x_3501_, v_a_3499_, v___y_3493_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3504_; lean_object* v_env_3505_; uint8_t v___x_3506_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = lean_st_ref_get(v___y_3496_);
v_env_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc_ref(v_env_3505_);
lean_dec(v___x_3504_);
v___x_3506_ = l_Lean_isStructure(v_env_3505_, v___x_3486_);
if (v___x_3506_ == 0)
{
size_t v_sz_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_sz_3507_ = lean_array_size(v_a_3503_);
v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(v_sz_3507_, v___x_3501_, v_a_3503_);
v___x_3509_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(v_a_3487_, v_params_3489_, v___x_3508_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec_ref(v___x_3508_);
return v___x_3509_;
}
else
{
size_t v_sz_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v_sz_3510_ = lean_array_size(v_a_3503_);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(v_sz_3510_, v___x_3501_, v_a_3503_);
v___x_3512_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(v_a_3487_, v_params_3489_, v___x_3511_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec_ref(v___x_3511_);
return v___x_3512_;
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_params_3489_);
lean_dec_ref(v_a_3487_);
lean_dec(v___x_3486_);
v_a_3513_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3502_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3502_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
v___jp_3521_:
{
if (lean_obj_tag(v___y_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___y_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___y_3522_, 1);
v_a_3499_ = v_a_3523_;
goto v___jp_3498_;
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref(v_params_3489_);
lean_dec_ref(v_a_3487_);
lean_dec(v___x_3486_);
v_a_3524_ = lean_ctor_get(v___y_3522_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___y_3522_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___y_3522_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___y_3522_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed(lean_object* v___x_3542_, lean_object* v_a_3543_, lean_object* v___x_3544_, lean_object* v_params_3545_, lean_object* v_x_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(v___x_3542_, v_a_3543_, v___x_3544_, v_params_3545_, v_x_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_x_3546_);
lean_dec(v___x_3544_);
return v_res_3554_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0);
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1);
v___x_3559_ = lean_unsigned_to_nat(0u);
v___x_3560_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
lean_ctor_set(v___x_3560_, 2, v___x_3559_);
lean_ctor_set(v___x_3560_, 3, v___x_3559_);
lean_ctor_set(v___x_3560_, 4, v___x_3558_);
lean_ctor_set(v___x_3560_, 5, v___x_3558_);
lean_ctor_set(v___x_3560_, 6, v___x_3558_);
lean_ctor_set(v___x_3560_, 7, v___x_3558_);
lean_ctor_set(v___x_3560_, 8, v___x_3558_);
lean_ctor_set(v___x_3560_, 9, v___x_3558_);
lean_ctor_set(v___x_3560_, 10, v___x_3558_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = lean_unsigned_to_nat(32u);
v___x_3562_ = lean_mk_empty_array_with_capacity(v___x_3561_);
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3564_ = ((size_t)5ULL);
v___x_3565_ = lean_unsigned_to_nat(0u);
v___x_3566_ = lean_unsigned_to_nat(32u);
v___x_3567_ = lean_mk_empty_array_with_capacity(v___x_3566_);
v___x_3568_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3);
v___x_3569_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set(v___x_3569_, 1, v___x_3567_);
lean_ctor_set(v___x_3569_, 2, v___x_3565_);
lean_ctor_set(v___x_3569_, 3, v___x_3565_);
lean_ctor_set_usize(v___x_3569_, 4, v___x_3564_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3570_ = lean_box(1);
v___x_3571_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4);
v___x_3572_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1);
v___x_3573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___x_3571_);
lean_ctor_set(v___x_3573_, 2, v___x_3570_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(lean_object* v_msgData_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; lean_object* v_env_3578_; lean_object* v___x_3579_; lean_object* v_scopes_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v_opts_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3577_ = lean_st_ref_get(v___y_3575_);
v_env_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc_ref(v_env_3578_);
lean_dec(v___x_3577_);
v___x_3579_ = lean_st_ref_get(v___y_3575_);
v_scopes_3580_ = lean_ctor_get(v___x_3579_, 2);
lean_inc(v_scopes_3580_);
lean_dec(v___x_3579_);
v___x_3581_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3582_ = l_List_head_x21___redArg(v___x_3581_, v_scopes_3580_);
lean_dec(v_scopes_3580_);
v_opts_3583_ = lean_ctor_get(v___x_3582_, 1);
lean_inc_ref(v_opts_3583_);
lean_dec(v___x_3582_);
v___x_3584_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2);
v___x_3585_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5);
v___x_3586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3586_, 0, v_env_3578_);
lean_ctor_set(v___x_3586_, 1, v___x_3584_);
lean_ctor_set(v___x_3586_, 2, v___x_3585_);
lean_ctor_set(v___x_3586_, 3, v_opts_3583_);
v___x_3587_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v_msgData_3574_);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___boxed(lean_object* v_msgData_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(v_msgData_3589_, v___y_3590_);
lean_dec(v___y_3590_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(lean_object* v_msgData_3593_, lean_object* v_macroStack_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v_scopes_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_opts_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; 
v___x_3597_ = lean_st_ref_get(v___y_3595_);
v_scopes_3598_ = lean_ctor_get(v___x_3597_, 2);
lean_inc(v_scopes_3598_);
lean_dec(v___x_3597_);
v___x_3599_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3600_ = l_List_head_x21___redArg(v___x_3599_, v_scopes_3598_);
lean_dec(v_scopes_3598_);
v_opts_3601_ = lean_ctor_get(v___x_3600_, 1);
lean_inc_ref(v_opts_3601_);
lean_dec(v___x_3600_);
v___x_3602_ = l_Lean_Elab_pp_macroStack;
v___x_3603_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__2(v_opts_3601_, v___x_3602_);
lean_dec_ref(v_opts_3601_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; 
lean_dec(v_macroStack_3594_);
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v_msgData_3593_);
return v___x_3604_;
}
else
{
if (lean_obj_tag(v_macroStack_3594_) == 0)
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3605_, 0, v_msgData_3593_);
return v___x_3605_;
}
else
{
lean_object* v_head_3606_; lean_object* v_after_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3622_; 
v_head_3606_ = lean_ctor_get(v_macroStack_3594_, 0);
lean_inc(v_head_3606_);
v_after_3607_ = lean_ctor_get(v_head_3606_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_head_3606_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_head_3606_, 0);
lean_dec(v_unused_3623_);
v___x_3609_ = v_head_3606_;
v_isShared_3610_ = v_isSharedCheck_3622_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_after_3607_);
lean_dec(v_head_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3622_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 7);
lean_ctor_set(v___x_3609_, 1, v___x_3611_);
lean_ctor_set(v___x_3609_, 0, v_msgData_3593_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_msgData_3593_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v_msgData_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3614_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1___redArg___closed__2);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_MessageData_ofSyntax(v_after_3607_);
v___x_3617_ = l_Lean_indentD(v___x_3616_);
v_msgData_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3618_, 0, v___x_3615_);
lean_ctor_set(v_msgData_3618_, 1, v___x_3617_);
v___x_3619_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0_spec__1_spec__3(v_msgData_3618_, v_macroStack_3594_);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg___boxed(lean_object* v_msgData_3624_, lean_object* v_macroStack_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(v_msgData_3624_, v_macroStack_3625_, v___y_3626_);
lean_dec(v___y_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(lean_object* v_msg_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_Elab_Command_getRef___redArg(v___y_3630_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v_macroStack_3635_; lean_object* v___x_3636_; lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3648_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v_macroStack_3635_ = lean_ctor_get(v___y_3630_, 4);
v___x_3636_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(v_msg_3629_, v___y_3631_);
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = l_Lean_Elab_getBetterRef(v_a_3634_, v_macroStack_3635_);
lean_dec(v_a_3634_);
lean_inc(v_macroStack_3635_);
v___x_3639_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(v_a_3637_, v_macroStack_3635_, v___y_3631_);
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3648_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3648_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3638_);
lean_ctor_set(v___x_3644_, 1, v_a_3640_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 1);
lean_ctor_set(v___x_3642_, 0, v___x_3644_);
v___x_3646_ = v___x_3642_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref(v_msg_3629_);
v_a_3649_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3633_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3633_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg___boxed(lean_object* v_msg_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v_msg_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3661_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0));
v___x_3664_ = l_Lean_stringToMessageData(v___x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(lean_object* v_constName_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; lean_object* v_env_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_st_ref_get(v___y_3667_);
v_env_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc_ref(v_env_3670_);
lean_dec(v___x_3669_);
lean_inc(v_constName_3665_);
v___x_3671_ = l_Lean_isInductiveCore_x3f(v_env_3670_, v_constName_3665_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3672_; uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3672_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___closed__1);
v___x_3673_ = 0;
v___x_3674_ = l_Lean_MessageData_ofConstName(v_constName_3665_, v___x_3673_);
v___x_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3672_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v___x_3677_, v___y_3666_, v___y_3667_);
return v___x_3678_;
}
else
{
lean_object* v_val_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_constName_3665_);
v_val_3679_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3671_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_val_3679_);
lean_dec(v___x_3671_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set_tag(v___x_3681_, 0);
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_val_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___boxed(lean_object* v_constName_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(v_constName_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3691_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0));
v___x_3694_ = l_Lean_stringToMessageData(v___x_3693_);
return v___x_3694_;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3(void){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2));
v___x_3697_ = l_Lean_stringToMessageData(v___x_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(lean_object* v_declNames_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3702_ = lean_array_get_size(v_declNames_3698_);
v___x_3703_ = lean_unsigned_to_nat(1u);
v___x_3704_ = lean_nat_dec_eq(v___x_3702_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_box(v___x_3704_);
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
return v___x_3706_;
}
else
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = lean_array_fget_borrowed(v_declNames_3698_, v___x_3707_);
lean_inc(v___x_3708_);
v___x_3709_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(v___x_3708_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v_toConstantVal_3711_; lean_object* v_numIndices_3712_; lean_object* v_all_3713_; lean_object* v___f_3714_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
v_toConstantVal_3711_ = lean_ctor_get(v_a_3710_, 0);
lean_inc_ref(v_toConstantVal_3711_);
v_numIndices_3712_ = lean_ctor_get(v_a_3710_, 2);
lean_inc(v_numIndices_3712_);
v_all_3713_ = lean_ctor_get(v_a_3710_, 3);
lean_inc(v_all_3713_);
lean_inc(v___x_3708_);
v___f_3714_ = lean_alloc_closure((void*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3714_, 0, v___x_3708_);
lean_closure_set(v___f_3714_, 1, v_a_3710_);
lean_closure_set(v___f_3714_, 2, v___x_3707_);
v___x_3765_ = l_List_lengthTR___redArg(v_all_3713_);
lean_dec(v_all_3713_);
v___x_3766_ = lean_nat_dec_eq(v___x_3765_, v___x_3703_);
lean_dec(v___x_3765_);
if (v___x_3766_ == 0)
{
if (v___x_3704_ == 0)
{
v___y_3752_ = v_a_3699_;
v___y_3753_ = v_a_3700_;
goto v___jp_3751_;
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v___f_3714_);
lean_dec(v_numIndices_3712_);
lean_dec_ref(v_toConstantVal_3711_);
v___x_3767_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3);
v___x_3768_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v___x_3767_, v_a_3699_, v_a_3700_);
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
v___y_3752_ = v_a_3699_;
v___y_3753_ = v_a_3700_;
goto v___jp_3751_;
}
v___jp_3715_:
{
lean_object* v_type_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_type_3718_ = lean_ctor_get(v_toConstantVal_3711_, 2);
lean_inc_ref(v_type_3718_);
lean_dec_ref(v_toConstantVal_3711_);
v___x_3719_ = 0;
v___x_3720_ = lean_box(v___x_3719_);
v___x_3721_ = lean_box(v___x_3719_);
v___x_3722_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed), 12, 5);
lean_closure_set(v___x_3722_, 0, lean_box(0));
lean_closure_set(v___x_3722_, 1, v_type_3718_);
lean_closure_set(v___x_3722_, 2, v___f_3714_);
lean_closure_set(v___x_3722_, 3, v___x_3720_);
lean_closure_set(v___x_3722_, 4, v___x_3721_);
v___x_3723_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_3722_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v___x_3725_ = l_Lean_Elab_Command_elabCommand(v_a_3724_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3733_; 
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v___x_3725_, 0);
lean_dec(v_unused_3734_);
v___x_3727_ = v___x_3725_;
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v___x_3725_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_box(v___x_3704_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3729_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_a_3735_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3725_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3725_);
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
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
v_a_3743_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3723_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3723_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
v___jp_3751_:
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_nat_dec_eq(v_numIndices_3712_, v___x_3707_);
lean_dec(v_numIndices_3712_);
if (v___x_3754_ == 0)
{
if (v___x_3704_ == 0)
{
v___y_3716_ = v___y_3752_;
v___y_3717_ = v___y_3753_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec_ref(v___f_3714_);
lean_dec_ref(v_toConstantVal_3711_);
v___x_3755_ = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1);
v___x_3756_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v___x_3755_, v___y_3752_, v___y_3753_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
v___y_3716_ = v___y_3752_;
v___y_3717_ = v___y_3753_;
goto v___jp_3715_;
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_a_3777_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3709_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3709_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed(lean_object* v_declNames_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(v_declNames_3785_, v_a_3786_, v_a_3787_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec_ref(v_declNames_3785_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(size_t v_sz_3790_, size_t v_i_3791_, lean_object* v_bs_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(v_sz_3790_, v_i_3791_, v_bs_3792_, v___y_3795_, v___y_3797_, v___y_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___boxed(lean_object* v_sz_3801_, lean_object* v_i_3802_, lean_object* v_bs_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
size_t v_sz_boxed_3811_; size_t v_i_boxed_3812_; lean_object* v_res_3813_; 
v_sz_boxed_3811_ = lean_unbox_usize(v_sz_3801_);
lean_dec(v_sz_3801_);
v_i_boxed_3812_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_res_3813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(v_sz_boxed_3811_, v_i_boxed_3812_, v_bs_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(lean_object* v_as_3814_, size_t v_i_3815_, size_t v_stop_3816_, lean_object* v_b_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(v_as_3814_, v_i_3815_, v_stop_3816_, v_b_3817_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___boxed(lean_object* v_as_3826_, lean_object* v_i_3827_, lean_object* v_stop_3828_, lean_object* v_b_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
size_t v_i_boxed_3837_; size_t v_stop_boxed_3838_; lean_object* v_res_3839_; 
v_i_boxed_3837_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_stop_boxed_3838_ = lean_unbox_usize(v_stop_3828_);
lean_dec(v_stop_3828_);
v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(v_as_3826_, v_i_boxed_3837_, v_stop_boxed_3838_, v_b_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_as_3826_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(lean_object* v_msgData_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(v_msgData_3840_, v___y_3842_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___boxed(lean_object* v_msgData_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(v_msgData_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(lean_object* v_00_u03b1_3850_, lean_object* v_msg_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(v_msg_3851_, v___y_3852_, v___y_3853_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___boxed(lean_object* v_00_u03b1_3856_, lean_object* v_msg_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(v_00_u03b1_3856_, v_msg_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(lean_object* v_msgData_3862_, lean_object* v_macroStack_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(v_msgData_3862_, v_macroStack_3863_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___boxed(lean_object* v_msgData_3868_, lean_object* v_macroStack_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(v_msgData_3868_, v_macroStack_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59));
v___x_3940_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_));
v___x_3941_ = l_Lean_Elab_registerDerivingHandler(v___x_3939_, v___x_3940_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_dec_ref_known(v___x_3941_, 1);
v___x_3942_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135));
v___x_3943_ = 0;
v___x_3944_ = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn___closed__25_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_));
v___x_3945_ = l_Lean_registerTraceClass(v___x_3942_, v___x_3943_, v___x_3944_);
return v___x_3945_;
}
else
{
return v___x_3941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2____boxed(lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_();
return v_res_3947_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
