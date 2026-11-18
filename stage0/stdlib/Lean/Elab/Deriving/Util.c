// Lean compiler output
// Module: Lean.Elab.Deriving.Util
// Imports: public import Lean.Elab.Command import Lean.Elab.DeclNameGen
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_instBinder;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_InductiveVal_isNested(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_implicitBinder(uint8_t);
lean_object* l_Lean_Parser_Term_explicitBinder(uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
static lean_once_cell_t l_Lean_Elab_Deriving_implicitBinderF___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_implicitBinderF___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_implicitBinderF;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_instBinderF;
static lean_once_cell_t l_Lean_Elab_Deriving_explicitBinderF___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_explicitBinderF___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_explicitBinderF;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Deriving_mkInductArgNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Deriving_mkInductArgNames___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductArgNames___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkImplicitBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value;
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value_aux_2),((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1_value;
static const lean_string_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value;
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value_aux_2),((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3_value;
static const lean_string_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value;
static const lean_string_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value;
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_1),((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value_aux_2),((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6_value;
static const lean_string_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expose"};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value;
static const lean_ctor_object l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(170, 113, 233, 77, 243, 78, 243, 129)}};
static const lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8_value;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "cannot use `deriving ... @[expose]` with `"};
static const lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2;
static const lean_string_object l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "` as it has one or more private constructors"};
static const lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_mkInstName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l_Lean_Elab_Deriving_mkInstName___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkInstName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_mkContext___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Deriving_mkContext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_mkContext___closed__5;
static const lean_string_object l_Lean_Elab_Deriving_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instName: "};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Deriving_mkContext___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_mkContext___closed__7;
static const lean_string_object l_Lean_Elab_Deriving_mkContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " auxFunNames: "};
static const lean_object* l_Lean_Elab_Deriving_mkContext___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_mkContext___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Deriving_mkContext___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_mkContext___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "localinst"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 72, 186, 87, 62, 92, 205, 11)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 166, 195, 152, 24, 103, 8, 2)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Deriving_groupByMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Deriving_groupByMutualBlock___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_groupByMutualBlock___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_groupByMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_groupByMutualBlock___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_groupByMutualBlock___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_groupByMutualBlock___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_groupByMutualBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_groupByMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_mkDiscr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Deriving_implicitBinderF___closed__0(void){
_start:
{
uint8_t v___x_1_; lean_object* v___x_2_; 
v___x_1_ = 0;
v___x_2_ = l_Lean_Parser_Term_implicitBinder(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_implicitBinderF(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_Lean_Elab_Deriving_implicitBinderF___closed__0, &l_Lean_Elab_Deriving_implicitBinderF___closed__0_once, _init_l_Lean_Elab_Deriving_implicitBinderF___closed__0);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_instBinderF(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Lean_Parser_Term_instBinder;
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_explicitBinderF___closed__0(void){
_start:
{
uint8_t v___x_5_; lean_object* v___x_6_; 
v___x_5_ = 0;
v___x_6_ = l_Lean_Parser_Term_explicitBinder(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_explicitBinderF(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Deriving_explicitBinderF___closed__0, &l_Lean_Elab_Deriving_explicitBinderF___closed__0_once, _init_l_Lean_Elab_Deriving_explicitBinderF___closed__0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(lean_object* v_k_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
v___x_18_ = lean_apply_9(v_k_8_, v_b_11_, v_c_12_, v___y_9_, v___y_10_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed(lean_object* v_k_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v_b_22_, lean_object* v_c_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(v_k_19_, v___y_20_, v___y_21_, v_b_22_, v_c_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(lean_object* v_type_30_, lean_object* v_k_31_, uint8_t v_cleanupAnnotations_32_, uint8_t v_whnfType_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___f_41_; lean_object* v___x_42_; 
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
v___f_41_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_41_, 0, v_k_31_);
lean_closure_set(v___f_41_, 1, v___y_34_);
lean_closure_set(v___f_41_, 2, v___y_35_);
v___x_42_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_30_, v___f_41_, v_cleanupAnnotations_32_, v_whnfType_33_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
if (lean_obj_tag(v___x_42_) == 0)
{
return v___x_42_;
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___boxed(lean_object* v_type_51_, lean_object* v_k_52_, lean_object* v_cleanupAnnotations_53_, lean_object* v_whnfType_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_62_; uint8_t v_whnfType_boxed_63_; lean_object* v_res_64_; 
v_cleanupAnnotations_boxed_62_ = lean_unbox(v_cleanupAnnotations_53_);
v_whnfType_boxed_63_ = lean_unbox(v_whnfType_54_);
v_res_64_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_51_, v_k_52_, v_cleanupAnnotations_boxed_62_, v_whnfType_boxed_63_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(lean_object* v_00_u03b1_65_, lean_object* v_type_66_, lean_object* v_k_67_, uint8_t v_cleanupAnnotations_68_, uint8_t v_whnfType_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_66_, v_k_67_, v_cleanupAnnotations_68_, v_whnfType_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___boxed(lean_object* v_00_u03b1_78_, lean_object* v_type_79_, lean_object* v_k_80_, lean_object* v_cleanupAnnotations_81_, lean_object* v_whnfType_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_90_; uint8_t v_whnfType_boxed_91_; lean_object* v_res_92_; 
v_cleanupAnnotations_boxed_90_ = lean_unbox(v_cleanupAnnotations_81_);
v_whnfType_boxed_91_ = lean_unbox(v_whnfType_82_);
v_res_92_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(v_00_u03b1_78_, v_type_79_, v_k_80_, v_cleanupAnnotations_boxed_90_, v_whnfType_boxed_91_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(lean_object* v_as_93_, size_t v_sz_94_, size_t v_i_95_, lean_object* v_b_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_lt(v_i_95_, v_sz_94_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v_b_96_);
return v___x_102_;
}
else
{
lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_a_103_ = lean_array_uget_borrowed(v_as_93_, v_i_95_);
v___x_104_ = l_Lean_Expr_fvarId_x21(v_a_103_);
v___x_105_ = l_Lean_FVarId_getDecl___redArg(v___x_104_, v___y_97_, v___y_98_, v___y_99_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = l_Lean_LocalDecl_userName(v_a_106_);
lean_dec(v_a_106_);
v___x_108_ = l_Lean_Name_eraseMacroScopes(v___x_107_);
lean_dec(v___x_107_);
v___x_109_ = l_Lean_Core_mkFreshUserName(v___x_108_, v___y_98_, v___y_99_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; size_t v___x_112_; size_t v___x_113_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
v___x_111_ = lean_array_push(v_b_96_, v_a_110_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_i_95_, v___x_112_);
v_i_95_ = v___x_113_;
v_b_96_ = v___x_111_;
goto _start;
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v_b_96_);
v_a_115_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_109_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_109_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec_ref(v_b_96_);
v_a_123_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_105_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_105_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg___boxed(lean_object* v_as_131_, lean_object* v_sz_132_, lean_object* v_i_133_, lean_object* v_b_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
size_t v_sz_boxed_139_; size_t v_i_boxed_140_; lean_object* v_res_141_; 
v_sz_boxed_139_ = lean_unbox_usize(v_sz_132_);
lean_dec(v_sz_132_);
v_i_boxed_140_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_131_, v_sz_boxed_139_, v_i_boxed_140_, v_b_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec_ref(v_as_131_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0(lean_object* v_xs_144_, lean_object* v_x_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_argNames_153_; size_t v_sz_154_; size_t v___x_155_; lean_object* v___x_156_; 
v_argNames_153_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v_sz_154_ = lean_array_size(v_xs_144_);
v___x_155_ = ((size_t)0ULL);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_xs_144_, v_sz_154_, v___x_155_, v_argNames_153_, v___y_148_, v___y_150_, v___y_151_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed(lean_object* v_xs_157_, lean_object* v_x_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0(v_xs_157_, v_x_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec_ref(v_x_158_);
lean_dec_ref(v_xs_157_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object* v_indVal_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_toConstantVal_176_; lean_object* v_type_177_; lean_object* v___f_178_; uint8_t v___x_179_; lean_object* v___x_180_; 
v_toConstantVal_176_ = lean_ctor_get(v_indVal_168_, 0);
lean_inc_ref(v_toConstantVal_176_);
lean_dec_ref(v_indVal_168_);
v_type_177_ = lean_ctor_get(v_toConstantVal_176_, 2);
lean_inc_ref(v_type_177_);
lean_dec_ref(v_toConstantVal_176_);
v___f_178_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___closed__0));
v___x_179_ = 0;
v___x_180_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_177_, v___f_178_, v___x_179_, v___x_179_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___boxed(lean_object* v_indVal_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(lean_object* v_as_190_, size_t v_sz_191_, size_t v_i_192_, lean_object* v_b_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_190_, v_sz_191_, v_i_192_, v_b_193_, v___y_196_, v___y_198_, v___y_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___boxed(lean_object* v_as_202_, lean_object* v_sz_203_, lean_object* v_i_204_, lean_object* v_b_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
size_t v_sz_boxed_213_; size_t v_i_boxed_214_; lean_object* v_res_215_; 
v_sz_boxed_213_ = lean_unbox_usize(v_sz_203_);
lean_dec(v_sz_203_);
v_i_boxed_214_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(v_as_202_, v_sz_boxed_213_, v_i_boxed_214_, v_b_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec_ref(v_as_202_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(size_t v_sz_216_, size_t v_i_217_, lean_object* v_bs_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_usize_dec_lt(v_i_217_, v_sz_216_);
if (v___x_219_ == 0)
{
return v_bs_218_;
}
else
{
lean_object* v_v_220_; lean_object* v___x_221_; lean_object* v_bs_x27_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v_v_220_ = lean_array_uget(v_bs_218_, v_i_217_);
v___x_221_ = lean_unsigned_to_nat(0u);
v_bs_x27_222_ = lean_array_uset(v_bs_218_, v_i_217_, v___x_221_);
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_add(v_i_217_, v___x_223_);
v___x_225_ = lean_array_uset(v_bs_x27_222_, v_i_217_, v_v_220_);
v_i_217_ = v___x_224_;
v_bs_218_ = v___x_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1___boxed(lean_object* v_sz_227_, lean_object* v_i_228_, lean_object* v_bs_229_){
_start:
{
size_t v_sz_boxed_230_; size_t v_i_boxed_231_; lean_object* v_res_232_; 
v_sz_boxed_230_ = lean_unbox_usize(v_sz_227_);
lean_dec(v_sz_227_);
v_i_boxed_231_ = lean_unbox_usize(v_i_228_);
lean_dec(v_i_228_);
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_boxed_230_, v_i_boxed_231_, v_bs_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(size_t v_sz_233_, size_t v_i_234_, lean_object* v_bs_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_236_ == 0)
{
return v_bs_235_;
}
else
{
lean_object* v_v_237_; lean_object* v___x_238_; lean_object* v_bs_x27_239_; lean_object* v___x_240_; size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; 
v_v_237_ = lean_array_uget(v_bs_235_, v_i_234_);
v___x_238_ = lean_unsigned_to_nat(0u);
v_bs_x27_239_ = lean_array_uset(v_bs_235_, v_i_234_, v___x_238_);
v___x_240_ = l_Lean_mkIdent(v_v_237_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_234_, v___x_241_);
v___x_243_ = lean_array_uset(v_bs_x27_239_, v_i_234_, v___x_240_);
v_i_234_ = v___x_242_;
v_bs_235_ = v___x_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0___boxed(lean_object* v_sz_245_, lean_object* v_i_246_, lean_object* v_bs_247_){
_start:
{
size_t v_sz_boxed_248_; size_t v_i_boxed_249_; lean_object* v_res_250_; 
v_sz_boxed_248_ = lean_unbox_usize(v_sz_245_);
lean_dec(v_sz_245_);
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_res_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_boxed_248_, v_i_boxed_249_, v_bs_247_);
return v_res_250_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Array_mkArray0___redArg();
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object* v_indVal_271_, lean_object* v_argNames_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_toConstantVal_275_; lean_object* v_name_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_302_; 
v_toConstantVal_275_ = lean_ctor_get(v_indVal_271_, 0);
lean_inc_ref(v_toConstantVal_275_);
lean_dec_ref(v_indVal_271_);
v_name_276_ = lean_ctor_get(v_toConstantVal_275_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_toConstantVal_275_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_303_ = lean_ctor_get(v_toConstantVal_275_, 2);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_toConstantVal_275_, 1);
lean_dec(v_unused_304_);
v___x_278_ = v_toConstantVal_275_;
v_isShared_279_ = v_isSharedCheck_302_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_name_276_);
lean_dec(v_toConstantVal_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_302_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_ref_280_; size_t v_sz_281_; lean_object* v_f_282_; size_t v___x_283_; lean_object* v_args_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; size_t v_sz_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v_ref_280_ = lean_ctor_get(v_a_273_, 2);
v_sz_281_ = lean_array_size(v_argNames_272_);
v_f_282_ = l_Lean_mkCIdent(v_name_276_);
v___x_283_ = ((size_t)0ULL);
v_args_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_281_, v___x_283_, v_argNames_272_);
v___x_285_ = 0;
v___x_286_ = l_Lean_SourceInfo_fromRef(v_ref_280_, v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
v___x_288_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6));
v___x_289_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7));
lean_inc_n(v___x_286_, 3);
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_286_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_Syntax_node2(v___x_286_, v___x_288_, v___x_290_, v_f_282_);
v___x_292_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_293_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v_sz_294_ = lean_array_size(v_args_284_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_294_, v___x_283_, v_args_284_);
v___x_296_ = l_Array_append___redArg(v___x_293_, v___x_295_);
lean_dec_ref(v___x_295_);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 2, v___x_296_);
lean_ctor_set(v___x_278_, 1, v___x_292_);
lean_ctor_set(v___x_278_, 0, v___x_286_);
v___x_298_ = v___x_278_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v___x_296_);
v___x_298_ = v_reuseFailAlloc_301_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_Syntax_node2(v___x_286_, v___x_287_, v___x_291_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___boxed(lean_object* v_indVal_305_, lean_object* v_argNames_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_305_, v_argNames_306_, v_a_307_);
lean_dec_ref(v_a_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp(lean_object* v_indVal_310_, lean_object* v_argNames_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_310_, v_argNames_311_, v_a_316_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___boxed(lean_object* v_indVal_320_, lean_object* v_argNames_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Elab_Deriving_mkInductiveApp(v_indVal_320_, v_argNames_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(size_t v_sz_338_, size_t v_i_339_, lean_object* v_bs_340_, lean_object* v___y_341_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_bs_340_);
return v___x_344_;
}
else
{
lean_object* v_ref_345_; lean_object* v_v_346_; lean_object* v___x_347_; lean_object* v_bs_x27_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; 
v_ref_345_ = lean_ctor_get(v___y_341_, 2);
v_v_346_ = lean_array_uget(v_bs_340_, v_i_339_);
v___x_347_ = lean_unsigned_to_nat(0u);
v_bs_x27_348_ = lean_array_uset(v_bs_340_, v_i_339_, v___x_347_);
v___x_349_ = 0;
v___x_350_ = l_Lean_SourceInfo_fromRef(v_ref_345_, v___x_349_);
v___x_351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1));
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2));
lean_inc_n(v___x_350_, 4);
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_355_ = l_Lean_mkIdent(v_v_346_);
v___x_356_ = l_Lean_Syntax_node1(v___x_350_, v___x_354_, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_358_, 0, v___x_350_);
lean_ctor_set(v___x_358_, 1, v___x_354_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3));
v___x_360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_350_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_Syntax_node4(v___x_350_, v___x_351_, v___x_353_, v___x_356_, v___x_358_, v___x_360_);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_add(v_i_339_, v___x_362_);
v___x_364_ = lean_array_uset(v_bs_x27_348_, v_i_339_, v___x_361_);
v_i_339_ = v___x_363_;
v_bs_340_ = v___x_364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___boxed(lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_bs_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_372_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_boxed_371_, v_i_boxed_372_, v_bs_368_, v___y_369_);
lean_dec_ref(v___y_369_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object* v_argNames_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
size_t v_sz_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_sz_382_ = lean_array_size(v_argNames_374_);
v___x_383_ = ((size_t)0ULL);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_382_, v___x_383_, v_argNames_374_, v_a_379_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkImplicitBinders___boxed(lean_object* v_argNames_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_argNames_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(size_t v_sz_394_, size_t v_i_395_, lean_object* v_bs_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_394_, v_i_395_, v_bs_396_, v___y_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___boxed(lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_bs_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
size_t v_sz_boxed_415_; size_t v_i_boxed_416_; lean_object* v_res_417_; 
v_sz_boxed_415_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_416_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(v_sz_boxed_415_, v_i_boxed_416_, v_bs_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(lean_object* v_type_418_, lean_object* v_maxFVars_x3f_419_, lean_object* v_k_420_, uint8_t v_cleanupAnnotations_421_, uint8_t v_whnfType_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; 
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_430_, 0, v_k_420_);
lean_closure_set(v___f_430_, 1, v___y_423_);
lean_closure_set(v___f_430_, 2, v___y_424_);
v___x_431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_418_, v_maxFVars_x3f_419_, v___f_430_, v_cleanupAnnotations_421_, v_whnfType_422_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_431_) == 0)
{
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg___boxed(lean_object* v_type_440_, lean_object* v_maxFVars_x3f_441_, lean_object* v_k_442_, lean_object* v_cleanupAnnotations_443_, lean_object* v_whnfType_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_452_; uint8_t v_whnfType_boxed_453_; lean_object* v_res_454_; 
v_cleanupAnnotations_boxed_452_ = lean_unbox(v_cleanupAnnotations_443_);
v_whnfType_boxed_453_ = lean_unbox(v_whnfType_444_);
v_res_454_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_440_, v_maxFVars_x3f_441_, v_k_442_, v_cleanupAnnotations_boxed_452_, v_whnfType_boxed_453_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(lean_object* v_00_u03b1_455_, lean_object* v_type_456_, lean_object* v_maxFVars_x3f_457_, lean_object* v_k_458_, uint8_t v_cleanupAnnotations_459_, uint8_t v_whnfType_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_456_, v_maxFVars_x3f_457_, v_k_458_, v_cleanupAnnotations_459_, v_whnfType_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___boxed(lean_object* v_00_u03b1_469_, lean_object* v_type_470_, lean_object* v_maxFVars_x3f_471_, lean_object* v_k_472_, lean_object* v_cleanupAnnotations_473_, lean_object* v_whnfType_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_482_; uint8_t v_whnfType_boxed_483_; lean_object* v_res_484_; 
v_cleanupAnnotations_boxed_482_ = lean_unbox(v_cleanupAnnotations_473_);
v_whnfType_boxed_483_ = lean_unbox(v_whnfType_474_);
v_res_484_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(v_00_u03b1_469_, v_type_470_, v_maxFVars_x3f_471_, v_k_472_, v_cleanupAnnotations_boxed_482_, v_whnfType_boxed_483_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(lean_object* v_upperBound_493_, lean_object* v_xs_494_, lean_object* v_className_495_, lean_object* v_argNames_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_snd_505_; lean_object* v_a_510_; uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_lt(v_a_497_, v_upperBound_493_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_dec(v_a_497_);
lean_dec(v_className_495_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_b_498_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_array_fget_borrowed(v_xs_494_, v_a_497_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_mk_empty_array_with_capacity(v___x_519_);
lean_inc(v___x_518_);
v___x_521_ = lean_array_push(v___x_520_, v___x_518_);
lean_inc(v_className_495_);
v___x_522_ = l_Lean_Meta_mkAppM(v_className_495_, v___x_521_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_Lean_Meta_isTypeCorrect(v_a_523_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; uint8_t v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = lean_unbox(v_a_525_);
lean_dec(v_a_525_);
if (v___x_526_ == 0)
{
v_snd_505_ = v_b_498_;
goto v___jp_504_;
}
else
{
lean_object* v_ref_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_ref_527_ = lean_ctor_get(v___y_501_, 2);
v___x_528_ = lean_array_get_borrowed(v___x_517_, v_argNames_496_, v_a_497_);
v___x_529_ = 0;
v___x_530_ = l_Lean_SourceInfo_fromRef(v_ref_527_, v___x_529_);
v___x_531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1));
v___x_532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2));
lean_inc_n(v___x_530_, 5);
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_535_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_536_, 0, v___x_530_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_495_);
v___x_538_ = l_Lean_mkCIdent(v_className_495_);
lean_inc(v___x_528_);
v___x_539_ = l_Lean_mkIdent(v___x_528_);
v___x_540_ = l_Lean_Syntax_node1(v___x_530_, v___x_534_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node2(v___x_530_, v___x_537_, v___x_538_, v___x_540_);
v___x_542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3));
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_530_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_Syntax_node4(v___x_530_, v___x_531_, v___x_533_, v___x_536_, v___x_541_, v___x_543_);
v___x_545_ = lean_array_push(v_b_498_, v___x_544_);
v_snd_505_ = v___x_545_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_524_, 1);
v_a_510_ = v_a_546_;
goto v___jp_509_;
}
}
else
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_522_, 1);
v_a_510_ = v_a_547_;
goto v___jp_509_;
}
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_a_497_, v___x_506_);
lean_dec(v_a_497_);
v_a_497_ = v___x_507_;
v_b_498_ = v_snd_505_;
goto _start;
}
v___jp_509_:
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_Exception_isInterrupt(v_a_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
lean_inc_ref(v_a_510_);
v___x_512_ = l_Lean_Exception_isRuntime(v_a_510_);
if (v___x_512_ == 0)
{
lean_dec_ref(v_a_510_);
v_snd_505_ = v_b_498_;
goto v___jp_504_;
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_b_498_);
lean_dec(v_a_497_);
lean_dec(v_className_495_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_a_510_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref(v_b_498_);
lean_dec(v_a_497_);
lean_dec(v_className_495_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_a_510_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___boxed(lean_object* v_upperBound_548_, lean_object* v_xs_549_, lean_object* v_className_550_, lean_object* v_argNames_551_, lean_object* v_a_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_548_, v_xs_549_, v_className_550_, v_argNames_551_, v_a_552_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec_ref(v_argNames_551_);
lean_dec_ref(v_xs_549_);
lean_dec(v_upperBound_548_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(lean_object* v_className_562_, lean_object* v_argNames_563_, lean_object* v_xs_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_binders_575_; lean_object* v___x_576_; 
v___x_573_ = lean_array_get_size(v_xs_564_);
v___x_574_ = lean_unsigned_to_nat(0u);
v_binders_575_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v___x_573_, v_xs_564_, v_className_562_, v_argNames_563_, v___x_574_, v_binders_575_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed(lean_object* v_className_577_, lean_object* v_argNames_578_, lean_object* v_xs_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(v_className_577_, v_argNames_578_, v_xs_579_, v_x_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v_x_580_);
lean_dec_ref(v_xs_579_);
lean_dec_ref(v_argNames_578_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object* v_className_589_, lean_object* v_indVal_590_, lean_object* v_argNames_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_toConstantVal_599_; lean_object* v_numParams_600_; lean_object* v_type_601_; lean_object* v___f_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; 
v_toConstantVal_599_ = lean_ctor_get(v_indVal_590_, 0);
lean_inc_ref(v_toConstantVal_599_);
v_numParams_600_ = lean_ctor_get(v_indVal_590_, 1);
lean_inc(v_numParams_600_);
lean_dec_ref(v_indVal_590_);
v_type_601_ = lean_ctor_get(v_toConstantVal_599_, 2);
lean_inc_ref(v_type_601_);
lean_dec_ref(v_toConstantVal_599_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed), 11, 2);
lean_closure_set(v___f_602_, 0, v_className_589_);
lean_closure_set(v___f_602_, 1, v_argNames_591_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v_numParams_600_);
v___x_604_ = 0;
v___x_605_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_601_, v___x_603_, v___f_602_, v___x_604_, v___x_604_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___boxed(lean_object* v_className_606_, lean_object* v_indVal_607_, lean_object* v_argNames_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_606_, v_indVal_607_, v_argNames_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(lean_object* v_upperBound_617_, lean_object* v_xs_618_, lean_object* v_className_619_, lean_object* v_argNames_620_, lean_object* v_inst_621_, lean_object* v_R_622_, lean_object* v_a_623_, lean_object* v_b_624_, lean_object* v_c_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_617_, v_xs_618_, v_className_619_, v_argNames_620_, v_a_623_, v_b_624_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___boxed(lean_object* v_upperBound_634_, lean_object* v_xs_635_, lean_object* v_className_636_, lean_object* v_argNames_637_, lean_object* v_inst_638_, lean_object* v_R_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v_c_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(v_upperBound_634_, v_xs_635_, v_className_636_, v_argNames_637_, v_inst_638_, v_R_639_, v_a_640_, v_b_641_, v_c_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v_argNames_637_);
lean_dec_ref(v_xs_635_);
lean_dec(v_upperBound_634_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(uint8_t v___x_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
if (lean_obj_tag(v_a_674_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_List_reverse___redArg(v_a_675_);
return v___x_676_;
}
else
{
lean_object* v_head_677_; lean_object* v_tail_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_707_; 
v_head_677_ = lean_ctor_get(v_a_674_, 0);
v_tail_678_ = lean_ctor_get(v_a_674_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_707_ == 0)
{
v___x_680_ = v_a_674_;
v_isShared_681_ = v_isSharedCheck_707_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_tail_678_);
lean_inc(v_head_677_);
lean_dec(v_a_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_707_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint8_t v___y_683_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1));
lean_inc(v_head_677_);
v___x_690_ = l_Lean_Syntax_isOfKind(v_head_677_, v___x_689_);
if (v___x_690_ == 0)
{
v___y_683_ = v___x_673_;
goto v___jp_682_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = l_Lean_Syntax_getArg(v_head_677_, v___x_691_);
v___x_693_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3));
lean_inc(v___x_692_);
v___x_694_ = l_Lean_Syntax_isOfKind(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_dec(v___x_692_);
v___y_683_ = v___x_673_;
goto v___jp_682_;
}
else
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = l_Lean_Syntax_getArg(v___x_692_, v___x_691_);
lean_dec(v___x_692_);
v___x_696_ = l_Lean_Syntax_matchesNull(v___x_695_, v___x_691_);
if (v___x_696_ == 0)
{
v___y_683_ = v___x_673_;
goto v___jp_682_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = l_Lean_Syntax_getArg(v_head_677_, v___x_697_);
v___x_699_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6));
lean_inc(v___x_698_);
v___x_700_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec(v___x_698_);
v___y_683_ = v___x_673_;
goto v___jp_682_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = l_Lean_Syntax_getArg(v___x_698_, v___x_691_);
v___x_702_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8));
v___x_703_ = l_Lean_Syntax_matchesIdent(v___x_701_, v___x_702_);
lean_dec(v___x_701_);
if (v___x_703_ == 0)
{
lean_dec(v___x_698_);
v___y_683_ = v___x_673_;
goto v___jp_682_;
}
else
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = l_Lean_Syntax_getArg(v___x_698_, v___x_697_);
lean_dec(v___x_698_);
v___x_705_ = l_Lean_Syntax_matchesNull(v___x_704_, v___x_691_);
if (v___x_705_ == 0)
{
v___y_683_ = v___x_673_;
goto v___jp_682_;
}
else
{
lean_del_object(v___x_680_);
lean_dec(v_head_677_);
v_a_674_ = v_tail_678_;
goto _start;
}
}
}
}
}
}
v___jp_682_:
{
if (v___y_683_ == 0)
{
lean_del_object(v___x_680_);
lean_dec(v_head_677_);
v_a_674_ = v_tail_678_;
goto _start;
}
else
{
lean_object* v___x_686_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_a_675_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_head_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_a_675_);
v___x_686_ = v_reuseFailAlloc_688_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v_a_674_ = v_tail_678_;
v_a_675_ = v___x_686_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___boxed(lean_object* v___x_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
uint8_t v___x_3732__boxed_711_; lean_object* v_res_712_; 
v___x_3732__boxed_711_ = lean_unbox(v___x_708_);
v_res_712_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_3732__boxed_711_, v_a_709_, v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(uint8_t v___x_713_, lean_object* v_sc_714_){
_start:
{
lean_object* v_header_715_; lean_object* v_opts_716_; lean_object* v_currNamespace_717_; lean_object* v_openDecls_718_; lean_object* v_levelNames_719_; lean_object* v_varDecls_720_; lean_object* v_varUIds_721_; lean_object* v_includedVars_722_; lean_object* v_omittedVars_723_; uint8_t v_isNoncomputable_724_; uint8_t v_isPublic_725_; uint8_t v_isMeta_726_; lean_object* v_attrs_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_header_715_ = lean_ctor_get(v_sc_714_, 0);
v_opts_716_ = lean_ctor_get(v_sc_714_, 1);
v_currNamespace_717_ = lean_ctor_get(v_sc_714_, 2);
v_openDecls_718_ = lean_ctor_get(v_sc_714_, 3);
v_levelNames_719_ = lean_ctor_get(v_sc_714_, 4);
v_varDecls_720_ = lean_ctor_get(v_sc_714_, 5);
v_varUIds_721_ = lean_ctor_get(v_sc_714_, 6);
v_includedVars_722_ = lean_ctor_get(v_sc_714_, 7);
v_omittedVars_723_ = lean_ctor_get(v_sc_714_, 8);
v_isNoncomputable_724_ = lean_ctor_get_uint8(v_sc_714_, sizeof(void*)*10);
v_isPublic_725_ = lean_ctor_get_uint8(v_sc_714_, sizeof(void*)*10 + 1);
v_isMeta_726_ = lean_ctor_get_uint8(v_sc_714_, sizeof(void*)*10 + 2);
v_attrs_727_ = lean_ctor_get(v_sc_714_, 9);
v_isSharedCheck_736_ = !lean_is_exclusive(v_sc_714_);
if (v_isSharedCheck_736_ == 0)
{
v___x_729_ = v_sc_714_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_attrs_727_);
lean_inc(v_omittedVars_723_);
lean_inc(v_includedVars_722_);
lean_inc(v_varUIds_721_);
lean_inc(v_varDecls_720_);
lean_inc(v_levelNames_719_);
lean_inc(v_openDecls_718_);
lean_inc(v_currNamespace_717_);
lean_inc(v_opts_716_);
lean_inc(v_header_715_);
lean_dec(v_sc_714_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_731_ = lean_box(0);
v___x_732_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_713_, v_attrs_727_, v___x_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 9, v___x_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_header_715_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_opts_716_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_currNamespace_717_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_openDecls_718_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_levelNames_719_);
lean_ctor_set(v_reuseFailAlloc_735_, 5, v_varDecls_720_);
lean_ctor_set(v_reuseFailAlloc_735_, 6, v_varUIds_721_);
lean_ctor_set(v_reuseFailAlloc_735_, 7, v_includedVars_722_);
lean_ctor_set(v_reuseFailAlloc_735_, 8, v_omittedVars_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 9, v___x_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_735_, sizeof(void*)*10, v_isNoncomputable_724_);
lean_ctor_set_uint8(v_reuseFailAlloc_735_, sizeof(void*)*10 + 1, v_isPublic_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_735_, sizeof(void*)*10 + 2, v_isMeta_726_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed(lean_object* v___x_737_, lean_object* v_sc_738_){
_start:
{
uint8_t v___x_3827__boxed_739_; lean_object* v_res_740_; 
v___x_3827__boxed_739_ = lean_unbox(v___x_737_);
v_res_740_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(v___x_3827__boxed_739_, v_sc_738_);
return v_res_740_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(1);
v___x_742_ = l_Lean_MessageData_ofFormat(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2));
v___x_747_ = l_Lean_MessageData_ofFormat(v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
return v_x_748_;
}
else
{
lean_object* v_head_750_; lean_object* v_tail_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_773_; 
v_head_750_ = lean_ctor_get(v_x_749_, 0);
v_tail_751_ = lean_ctor_get(v_x_749_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_773_ == 0)
{
v___x_753_ = v_x_749_;
v_isShared_754_ = v_isSharedCheck_773_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_tail_751_);
lean_inc(v_head_750_);
lean_dec(v_x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_773_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_before_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_771_; 
v_before_755_ = lean_ctor_get(v_head_750_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_head_750_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_head_750_, 1);
lean_dec(v_unused_772_);
v___x_757_ = v_head_750_;
v_isShared_758_ = v_isSharedCheck_771_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_before_755_);
lean_dec(v_head_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_771_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 7);
lean_ctor_set(v___x_757_, 1, v___x_759_);
lean_ctor_set(v___x_757_, 0, v_x_748_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_x_748_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_770_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 7);
lean_ctor_set(v___x_753_, 1, v___x_762_);
lean_ctor_set(v___x_753_, 0, v___x_761_);
v___x_764_ = v___x_753_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_769_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = l_Lean_MessageData_ofSyntax(v_before_755_);
v___x_766_ = l_Lean_indentD(v___x_765_);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_764_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v_x_748_ = v___x_767_;
v_x_749_ = v_tail_751_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(lean_object* v_opts_774_, lean_object* v_opt_775_){
_start:
{
lean_object* v_name_776_; lean_object* v_defValue_777_; lean_object* v_map_778_; lean_object* v___x_779_; 
v_name_776_ = lean_ctor_get(v_opt_775_, 0);
v_defValue_777_ = lean_ctor_get(v_opt_775_, 1);
v_map_778_ = lean_ctor_get(v_opts_774_, 0);
v___x_779_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_778_, v_name_776_);
if (lean_obj_tag(v___x_779_) == 0)
{
uint8_t v___x_780_; 
v___x_780_ = lean_unbox(v_defValue_777_);
return v___x_780_;
}
else
{
lean_object* v_val_781_; 
v_val_781_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_781_);
lean_dec_ref_known(v___x_779_, 1);
if (lean_obj_tag(v_val_781_) == 1)
{
uint8_t v_v_782_; 
v_v_782_ = lean_ctor_get_uint8(v_val_781_, 0);
lean_dec_ref_known(v_val_781_, 0);
return v_v_782_;
}
else
{
uint8_t v___x_783_; 
lean_dec(v_val_781_);
v___x_783_ = lean_unbox(v_defValue_777_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_784_, lean_object* v_opt_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_784_, v_opt_785_);
lean_dec_ref(v_opt_785_);
lean_dec_ref(v_opts_784_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1));
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(lean_object* v_msgData_793_, lean_object* v_macroStack_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_scopes_799_; lean_object* v___x_800_; lean_object* v_opts_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_797_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_798_ = lean_st_ref_get(v___y_795_);
v_scopes_799_ = lean_ctor_get(v___x_798_, 2);
lean_inc(v_scopes_799_);
lean_dec(v___x_798_);
v___x_800_ = l_List_head_x21___redArg(v___x_797_, v_scopes_799_);
lean_dec(v_scopes_799_);
v_opts_801_ = lean_ctor_get(v___x_800_, 1);
lean_inc_ref(v_opts_801_);
lean_dec(v___x_800_);
v___x_802_ = l_Lean_Elab_pp_macroStack;
v___x_803_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_801_, v___x_802_);
lean_dec_ref(v_opts_801_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_macroStack_794_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_msgData_793_);
return v___x_804_;
}
else
{
if (lean_obj_tag(v_macroStack_794_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_msgData_793_);
return v___x_805_;
}
else
{
lean_object* v_head_806_; lean_object* v_after_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_822_; 
v_head_806_ = lean_ctor_get(v_macroStack_794_, 0);
lean_inc(v_head_806_);
v_after_807_ = lean_ctor_get(v_head_806_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_head_806_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_head_806_, 0);
lean_dec(v_unused_823_);
v___x_809_ = v_head_806_;
v_isShared_810_ = v_isSharedCheck_822_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_after_807_);
lean_dec(v_head_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_822_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 7);
lean_ctor_set(v___x_809_, 1, v___x_811_);
lean_ctor_set(v___x_809_, 0, v_msgData_793_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_msgData_793_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_821_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_msgData_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_814_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_MessageData_ofSyntax(v_after_807_);
v___x_817_ = l_Lean_indentD(v___x_816_);
v_msgData_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_818_, 0, v___x_815_);
lean_ctor_set(v_msgData_818_, 1, v___x_817_);
v___x_819_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_818_, v_macroStack_794_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_824_, lean_object* v_macroStack_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_824_, v_macroStack_825_, v___y_826_);
lean_dec(v___y_826_);
return v_res_828_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_829_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
lean_ctor_set(v___x_834_, 2, v___x_833_);
lean_ctor_set(v___x_834_, 3, v___x_833_);
lean_ctor_set(v___x_834_, 4, v___x_832_);
lean_ctor_set(v___x_834_, 5, v___x_832_);
lean_ctor_set(v___x_834_, 6, v___x_832_);
lean_ctor_set(v___x_834_, 7, v___x_832_);
lean_ctor_set(v___x_834_, 8, v___x_832_);
lean_ctor_set(v___x_834_, 9, v___x_832_);
lean_ctor_set(v___x_834_, 10, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_unsigned_to_nat(32u);
v___x_836_ = lean_mk_empty_array_with_capacity(v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_838_ = ((size_t)5ULL);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_unsigned_to_nat(32u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3);
v___x_843_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v___x_841_);
lean_ctor_set(v___x_843_, 2, v___x_839_);
lean_ctor_set(v___x_843_, 3, v___x_839_);
lean_ctor_set_usize(v___x_843_, 4, v___x_838_);
return v___x_843_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_844_ = lean_box(1);
v___x_845_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4);
v___x_846_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
v___x_847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_845_);
lean_ctor_set(v___x_847_, 2, v___x_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(lean_object* v_msgData_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_env_852_; uint8_t v___x_853_; lean_object* v_env_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_scopes_857_; lean_object* v___x_858_; lean_object* v_opts_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_851_ = lean_st_ref_get(v___y_849_);
v_env_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_env_852_);
lean_dec(v___x_851_);
v___x_853_ = 0;
v_env_854_ = l_Lean_Environment_setRecordingDeps(v_env_852_, v___x_853_);
v___x_855_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_856_ = lean_st_ref_get(v___y_849_);
v_scopes_857_ = lean_ctor_get(v___x_856_, 2);
lean_inc(v_scopes_857_);
lean_dec(v___x_856_);
v___x_858_ = l_List_head_x21___redArg(v___x_855_, v_scopes_857_);
lean_dec(v_scopes_857_);
v_opts_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc_ref(v_opts_859_);
lean_dec(v___x_858_);
v___x_860_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2);
v___x_861_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5);
v___x_862_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_862_, 0, v_env_854_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
lean_ctor_set(v___x_862_, 3, v_opts_859_);
v___x_863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v_msgData_848_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_865_, v___y_866_);
lean_dec(v___y_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(lean_object* v_msg_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Elab_Command_getRef___redArg(v___y_870_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v_macroStack_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v_macroStack_875_ = lean_ctor_get(v___y_870_, 4);
v___x_876_ = l_Lean_Elab_getBetterRef(v_a_874_, v_macroStack_875_);
lean_dec(v_a_874_);
v___x_877_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msg_869_, v___y_871_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
lean_inc(v_macroStack_875_);
v___x_879_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_a_878_, v_macroStack_875_, v___y_871_);
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_876_);
lean_ctor_set(v___x_884_, 1, v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 1);
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v_msg_869_);
v_a_889_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_873_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_873_);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg___boxed(lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(lean_object* v_constName_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; lean_object* v_env_913_; lean_object* v___x_914_; 
v___x_912_ = lean_st_ref_get(v___y_910_);
v_env_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_env_913_);
lean_dec(v___x_912_);
lean_inc(v_constName_908_);
v___x_914_ = l_Lean_isInductiveCore_x3f(v_env_913_, v_constName_908_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_915_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_916_ = 0;
v___x_917_ = l_Lean_MessageData_ofConstName(v_constName_908_, v___x_916_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_915_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_920_, v___y_909_, v___y_910_);
return v___x_921_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_constName_908_);
v_val_922_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_914_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_val_922_);
lean_dec(v___x_914_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 0);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_val_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___boxed(lean_object* v_constName_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_constName_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(lean_object* v_as_x27_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
if (lean_obj_tag(v_as_x27_935_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_936_);
return v___x_940_;
}
else
{
lean_object* v_head_941_; lean_object* v_tail_942_; lean_object* v___x_943_; 
v_head_941_ = lean_ctor_get(v_as_x27_935_, 0);
v_tail_942_ = lean_ctor_get(v_as_x27_935_, 1);
lean_inc(v_head_941_);
v___x_943_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_head_941_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = lean_array_push(v_b_936_, v_a_944_);
v_as_x27_935_ = v_tail_942_;
v_b_936_ = v___x_945_;
goto _start;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_b_936_);
v_a_947_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_943_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_943_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg___boxed(lean_object* v_as_x27_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_955_, v_b_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_as_x27_955_);
return v_res_960_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(lean_object* v___y_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
uint8_t v___x_963_; 
v___x_963_ = 0;
return v___x_963_;
}
else
{
lean_object* v_head_964_; lean_object* v_tail_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_head_964_ = lean_ctor_get(v_x_962_, 0);
lean_inc_n(v_head_964_, 2);
v_tail_965_ = lean_ctor_get(v_x_962_, 1);
lean_inc(v_tail_965_);
lean_dec_ref_known(v_x_962_, 2);
v___x_966_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1));
v___x_967_ = l_Lean_Syntax_isOfKind(v_head_964_, v___x_966_);
if (v___x_967_ == 0)
{
lean_dec(v_head_964_);
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = l_Lean_Syntax_getArg(v_head_964_, v___x_969_);
v___x_971_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3));
lean_inc(v___x_970_);
v___x_972_ = l_Lean_Syntax_isOfKind(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_dec(v___x_970_);
lean_dec(v_head_964_);
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = l_Lean_Syntax_getArg(v___x_970_, v___x_969_);
lean_dec(v___x_970_);
v___x_975_ = l_Lean_Syntax_matchesNull(v___x_974_, v___x_969_);
if (v___x_975_ == 0)
{
lean_dec(v_head_964_);
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = l_Lean_Syntax_getArg(v_head_964_, v___x_977_);
lean_dec(v_head_964_);
v___x_979_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6));
lean_inc(v___x_978_);
v___x_980_ = l_Lean_Syntax_isOfKind(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
lean_dec(v___x_978_);
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = l_Lean_Syntax_getArg(v___x_978_, v___x_969_);
v___x_983_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8));
v___x_984_ = l_Lean_Syntax_matchesIdent(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
if (v___x_984_ == 0)
{
lean_dec(v___x_978_);
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = l_Lean_Syntax_getArg(v___x_978_, v___x_977_);
lean_dec(v___x_978_);
v___x_987_ = l_Lean_Syntax_matchesNull(v___x_986_, v___x_969_);
if (v___x_987_ == 0)
{
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_lt(v___x_969_, v___y_961_);
if (v___x_989_ == 0)
{
v_x_962_ = v_tail_965_;
goto _start;
}
else
{
lean_dec(v_tail_965_);
return v___x_989_;
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
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5___boxed(lean_object* v___y_991_, lean_object* v_x_992_){
_start:
{
uint8_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___y_991_, v_x_992_);
lean_dec(v___y_991_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(lean_object* v_x_995_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
uint8_t v___x_996_; 
v___x_996_ = 0;
return v___x_996_;
}
else
{
lean_object* v_head_997_; lean_object* v_tail_998_; uint8_t v___x_999_; 
v_head_997_ = lean_ctor_get(v_x_995_, 0);
v_tail_998_ = lean_ctor_get(v_x_995_, 1);
v___x_999_ = l_Lean_isPrivateName(v_head_997_);
if (v___x_999_ == 0)
{
v_x_995_ = v_tail_998_;
goto _start;
}
else
{
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0___boxed(lean_object* v_x_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_x_1001_);
lean_dec(v_x_1001_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(lean_object* v_as_1004_, size_t v_i_1005_, size_t v_stop_1006_){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_usize_dec_eq(v_i_1005_, v_stop_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v_ctors_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_array_uget_borrowed(v_as_1004_, v_i_1005_);
v_ctors_1009_ = lean_ctor_get(v___x_1008_, 4);
v___x_1010_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_ctors_1009_);
if (v___x_1010_ == 0)
{
size_t v___x_1011_; size_t v___x_1012_; 
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_add(v_i_1005_, v___x_1011_);
v_i_1005_ = v___x_1012_;
goto _start;
}
else
{
return v___x_1010_;
}
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = 0;
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3___boxed(lean_object* v_as_1015_, lean_object* v_i_1016_, lean_object* v_stop_1017_){
_start:
{
size_t v_i_boxed_1018_; size_t v_stop_boxed_1019_; uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_i_boxed_1018_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_stop_boxed_1019_ = lean_unbox_usize(v_stop_1017_);
lean_dec(v_stop_1017_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_as_1015_, v_i_boxed_1018_, v_stop_boxed_1019_);
lean_dec_ref(v_as_1015_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object* v_typeName_1030_, lean_object* v_cont_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
lean_inc(v_typeName_1030_);
v___x_1035_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_typeName_1030_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v_all_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v_all_1037_ = lean_ctor_get(v_a_1036_, 3);
lean_inc(v_all_1037_);
lean_dec(v_a_1036_);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1040_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_all_1037_, v___x_1039_, v_a_1032_, v_a_1033_);
lean_dec(v_all_1037_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = lean_array_get_size(v_a_1041_);
v___x_1043_ = lean_nat_dec_lt(v___x_1038_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec(v_a_1041_);
lean_dec(v_typeName_1030_);
lean_inc(v_a_1033_);
lean_inc_ref(v_a_1032_);
v___x_1044_ = lean_apply_3(v_cont_1031_, v_a_1032_, v_a_1033_, lean_box(0));
return v___x_1044_;
}
else
{
if (v___x_1043_ == 0)
{
lean_object* v___x_1045_; 
lean_dec(v_a_1041_);
lean_dec(v_typeName_1030_);
lean_inc(v_a_1033_);
lean_inc_ref(v_a_1032_);
v___x_1045_ = lean_apply_3(v_cont_1031_, v_a_1032_, v_a_1033_, lean_box(0));
return v___x_1045_;
}
else
{
size_t v___x_1046_; size_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = lean_usize_of_nat(v___x_1042_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_a_1041_, v___x_1046_, v___x_1047_);
lean_dec(v_a_1041_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec(v_typeName_1030_);
lean_inc(v_a_1033_);
lean_inc_ref(v_a_1032_);
v___x_1049_ = lean_apply_3(v_cont_1031_, v_a_1032_, v_a_1033_, lean_box(0));
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___f_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_box(v___x_1048_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1051_, 0, v___x_1050_);
v___x_1052_ = l_Lean_isPrivateName(v_typeName_1030_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Elab_Command_getScope___redArg(v_a_1033_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_attrs_1055_; uint8_t v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v_attrs_1055_ = lean_ctor_get(v_a_1054_, 9);
lean_inc(v_attrs_1055_);
lean_dec(v_a_1054_);
v___x_1056_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___x_1042_, v_attrs_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec(v_typeName_1030_);
v___x_1057_ = l_Lean_Elab_Command_withScope___redArg(v___f_1051_, v_cont_1031_, v_a_1032_, v_a_1033_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v___f_1051_);
lean_dec_ref(v_cont_1031_);
v___x_1058_ = lean_obj_once(&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2, &l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once, _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2);
v___x_1059_ = l_Lean_MessageData_ofConstName(v_typeName_1030_, v___x_1052_);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4, &l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once, _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_1062_, v_a_1032_, v_a_1033_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___f_1051_);
lean_dec_ref(v_cont_1031_);
lean_dec(v_typeName_1030_);
v_a_1072_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1053_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1053_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v___x_1080_; 
lean_dec(v_typeName_1030_);
v___x_1080_ = l_Lean_Elab_Command_withScope___redArg(v___f_1051_, v_cont_1031_, v_a_1032_, v_a_1033_);
return v___x_1080_;
}
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_cont_1031_);
lean_dec(v_typeName_1030_);
v_a_1081_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1040_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1040_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_cont_1031_);
lean_dec(v_typeName_1030_);
v_a_1089_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1035_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1035_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___boxed(lean_object* v_typeName_1097_, lean_object* v_cont_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1097_, v_cont_1098_, v_a_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors(lean_object* v_00_u03b1_1103_, lean_object* v_typeName_1104_, lean_object* v_cont_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1104_, v_cont_1105_, v_a_1106_, v_a_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_typeName_1111_, lean_object* v_cont_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Elab_Deriving_withoutExposeFromCtors(v_00_u03b1_1110_, v_typeName_1111_, v_cont_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(lean_object* v_as_1117_, lean_object* v_as_x27_1118_, lean_object* v_b_1119_, lean_object* v_a_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_1118_, v_b_1119_, v___y_1121_, v___y_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___boxed(lean_object* v_as_1125_, lean_object* v_as_x27_1126_, lean_object* v_b_1127_, lean_object* v_a_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(v_as_1125_, v_as_x27_1126_, v_b_1127_, v_a_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v_as_x27_1126_);
lean_dec(v_as_1125_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(lean_object* v_msgData_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_1133_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___boxed(lean_object* v_msgData_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(v_msgData_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(lean_object* v_00_u03b1_1143_, lean_object* v_msg_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_1144_, v___y_1145_, v___y_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___boxed(lean_object* v_00_u03b1_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(v_00_u03b1_1149_, v_msg_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(lean_object* v_msgData_1155_, lean_object* v_macroStack_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_1155_, v_macroStack_1156_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___boxed(lean_object* v_msgData_1161_, lean_object* v_macroStack_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(v_msgData_1161_, v_macroStack_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___lam__0(lean_object* v___x_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v___x_1167_, v_b_1168_, v___y_1169_, v___y_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___lam__0___boxed(lean_object* v___x_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___lam__0(v___x_1173_, v_b_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg(lean_object* v_as_1179_, size_t v_i_1180_, size_t v_stop_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_eq(v_i_1180_, v_stop_1181_);
if (v___x_1186_ == 0)
{
size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; 
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_sub(v_i_1180_, v___x_1187_);
v___x_1189_ = lean_array_uget_borrowed(v_as_1179_, v___x_1188_);
lean_inc(v___x_1189_);
v___f_1190_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1190_, 0, v___x_1189_);
lean_closure_set(v___f_1190_, 1, v_b_1182_);
v_i_1180_ = v___x_1188_;
v_b_1182_ = v___f_1190_;
goto _start;
}
else
{
lean_object* v___x_1192_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1192_ = lean_apply_3(v_b_1182_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg___boxed(lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_stop_1195_, lean_object* v_b_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_i_boxed_1200_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1195_);
lean_dec(v_stop_1195_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg(v_as_1193_, v_i_boxed_1200_, v_stop_boxed_1201_, v_b_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v_as_1193_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___redArg(lean_object* v_typeNames_1203_, lean_object* v_cont_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = lean_array_get_size(v_typeNames_1203_);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_nat_dec_lt(v___x_1209_, v___x_1208_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_inc(v_a_1206_);
lean_inc_ref(v_a_1205_);
v___x_1211_ = lean_apply_3(v_cont_1204_, v_a_1205_, v_a_1206_, lean_box(0));
return v___x_1211_;
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_usize_of_nat(v___x_1208_);
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg(v_typeNames_1203_, v___x_1212_, v___x_1213_, v_cont_1204_, v_a_1205_, v_a_1206_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___redArg___boxed(lean_object* v_typeNames_1215_, lean_object* v_cont_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___redArg(v_typeNames_1215_, v_cont_1216_, v_a_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v_typeNames_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll(lean_object* v_00_u03b1_1221_, lean_object* v_typeNames_1222_, lean_object* v_cont_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___redArg(v_typeNames_1222_, v_cont_1223_, v_a_1224_, v_a_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtorsAll___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_typeNames_1229_, lean_object* v_cont_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Elab_Deriving_withoutExposeFromCtorsAll(v_00_u03b1_1228_, v_typeNames_1229_, v_cont_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec_ref(v_typeNames_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0(lean_object* v_00_u03b1_1235_, lean_object* v_as_1236_, size_t v_i_1237_, size_t v_stop_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___redArg(v_as_1236_, v_i_1237_, v_stop_1238_, v_b_1239_, v___y_1240_, v___y_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_as_1245_, lean_object* v_i_1246_, lean_object* v_stop_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
size_t v_i_boxed_1252_; size_t v_stop_boxed_1253_; lean_object* v_res_1254_; 
v_i_boxed_1252_ = lean_unbox_usize(v_i_1246_);
lean_dec(v_i_1246_);
v_stop_boxed_1253_ = lean_unbox_usize(v_stop_1247_);
lean_dec(v_stop_1247_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_withoutExposeFromCtorsAll_spec__0(v_00_u03b1_1244_, v_as_1245_, v_i_boxed_1252_, v_stop_boxed_1253_, v_b_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v_as_1245_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(size_t v_sz_1255_, size_t v_i_1256_, lean_object* v_bs_1257_){
_start:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_usize_dec_lt(v_i_1256_, v_sz_1255_);
if (v___x_1258_ == 0)
{
return v_bs_1257_;
}
else
{
lean_object* v_v_1259_; lean_object* v___x_1260_; lean_object* v_bs_x27_1261_; size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v_v_1259_ = lean_array_uget(v_bs_1257_, v_i_1256_);
v___x_1260_ = lean_unsigned_to_nat(0u);
v_bs_x27_1261_ = lean_array_uset(v_bs_1257_, v_i_1256_, v___x_1260_);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1256_, v___x_1262_);
v___x_1264_ = lean_array_uset(v_bs_x27_1261_, v_i_1256_, v_v_1259_);
v_i_1256_ = v___x_1263_;
v_bs_1257_ = v___x_1264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1___boxed(lean_object* v_sz_1266_, lean_object* v_i_1267_, lean_object* v_bs_1268_){
_start:
{
size_t v_sz_boxed_1269_; size_t v_i_boxed_1270_; lean_object* v_res_1271_; 
v_sz_boxed_1269_ = lean_unbox_usize(v_sz_1266_);
lean_dec(v_sz_1266_);
v_i_boxed_1270_ = lean_unbox_usize(v_i_1267_);
lean_dec(v_i_1267_);
v_res_1271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_boxed_1269_, v_i_boxed_1270_, v_bs_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(lean_object* v_msgData_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_env_1279_; uint8_t v___x_1280_; lean_object* v_env_1281_; lean_object* v___x_1282_; lean_object* v_toCold_1283_; lean_object* v_mctx_1284_; lean_object* v_lctx_1285_; lean_object* v_options_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1278_ = lean_st_ref_get(v___y_1276_);
v_env_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc_ref(v_env_1279_);
lean_dec(v___x_1278_);
v___x_1280_ = 0;
v_env_1281_ = l_Lean_Environment_setRecordingDeps(v_env_1279_, v___x_1280_);
v___x_1282_ = lean_st_ref_get(v___y_1274_);
v_toCold_1283_ = lean_ctor_get(v___y_1275_, 0);
v_mctx_1284_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_mctx_1284_);
lean_dec(v___x_1282_);
v_lctx_1285_ = lean_ctor_get(v___y_1273_, 2);
v_options_1286_ = lean_ctor_get(v_toCold_1283_, 2);
lean_inc_ref(v_options_1286_);
lean_inc_ref(v_lctx_1285_);
v___x_1287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1287_, 0, v_env_1281_);
lean_ctor_set(v___x_1287_, 1, v_mctx_1284_);
lean_ctor_set(v___x_1287_, 2, v_lctx_1285_);
lean_ctor_set(v___x_1287_, 3, v_options_1286_);
v___x_1288_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_msgData_1272_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1297_, lean_object* v_macroStack_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1299_);
v___x_1302_ = l_Lean_Elab_pp_macroStack;
v___x_1303_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v___x_1301_, v___x_1302_);
lean_dec_ref(v___x_1301_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_macroStack_1298_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_msgData_1297_);
return v___x_1304_;
}
else
{
if (lean_obj_tag(v_macroStack_1298_) == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_msgData_1297_);
return v___x_1305_;
}
else
{
lean_object* v_head_1306_; lean_object* v_after_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1322_; 
v_head_1306_ = lean_ctor_get(v_macroStack_1298_, 0);
lean_inc(v_head_1306_);
v_after_1307_ = lean_ctor_get(v_head_1306_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_head_1306_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_head_1306_, 0);
lean_dec(v_unused_1323_);
v___x_1309_ = v_head_1306_;
v_isShared_1310_ = v_isSharedCheck_1322_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_after_1307_);
lean_dec(v_head_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1322_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 7);
lean_ctor_set(v___x_1309_, 1, v___x_1311_);
lean_ctor_set(v___x_1309_, 0, v_msgData_1297_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_msgData_1297_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_msgData_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1314_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_MessageData_ofSyntax(v_after_1307_);
v___x_1317_ = l_Lean_indentD(v___x_1316_);
v_msgData_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1318_, 0, v___x_1315_);
lean_ctor_set(v_msgData_1318_, 1, v___x_1317_);
v___x_1319_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_1318_, v_macroStack_1298_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1324_, lean_object* v_macroStack_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1324_, v_macroStack_1325_, v___y_1326_);
lean_dec_ref(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_ref_1337_; lean_object* v_macroStack_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_ref_1337_ = lean_ctor_get(v___y_1334_, 2);
v_macroStack_1338_ = lean_ctor_get(v___y_1330_, 1);
v___x_1339_ = l_Lean_Elab_getBetterRef(v_ref_1337_, v_macroStack_1338_);
v___x_1340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1329_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1340_);
lean_inc(v_macroStack_1338_);
v___x_1342_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_a_1341_, v_macroStack_1338_, v___y_1334_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1339_);
lean_ctor_set(v___x_1347_, 1, v_a_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 1);
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(lean_object* v_constName_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_env_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_st_ref_get(v___y_1367_);
v_env_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc_ref(v_env_1370_);
lean_dec(v___x_1369_);
lean_inc(v_constName_1361_);
v___x_1371_ = l_Lean_isInductiveCore_x3f(v_env_1370_, v_constName_1361_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1372_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_1373_ = 0;
v___x_1374_ = l_Lean_MessageData_ofConstName(v_constName_1361_, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1372_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v___x_1377_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1378_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_constName_1361_);
v_val_1379_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1371_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_val_1379_);
lean_dec(v___x_1371_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 0);
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_val_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0___boxed(lean_object* v_constName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object* v_className_1397_, lean_object* v_indName_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_indName_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_n(v_a_1407_, 2);
lean_dec_ref_known(v___x_1406_, 1);
v___x_1408_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_1407_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_n(v_a_1409_, 2);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_1409_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v_ref_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_1407_, v_a_1409_, v_a_1403_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v_ref_1414_ = lean_ctor_get(v_a_1403_, 2);
v___x_1415_ = 0;
v___x_1416_ = l_Lean_SourceInfo_fromRef(v_ref_1414_, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
v___x_1418_ = l_Lean_mkCIdent(v_className_1397_);
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1416_);
v___x_1420_ = l_Lean_Syntax_node1(v___x_1416_, v___x_1419_, v_a_1413_);
v___x_1421_ = l_Lean_Syntax_node2(v___x_1416_, v___x_1417_, v___x_1418_, v___x_1420_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstName___closed__0));
v_sz_1423_ = lean_array_size(v_a_1411_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_1423_, v___x_1424_, v_a_1411_);
v___x_1426_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_1422_, v___x_1425_, v___x_1421_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1426_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_a_1409_);
lean_dec(v_a_1407_);
lean_dec(v_className_1397_);
v_a_1427_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1410_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1410_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1407_);
lean_dec(v_className_1397_);
v_a_1435_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1408_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1408_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_className_1397_);
v_a_1443_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1406_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1406_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName___boxed(lean_object* v_className_1451_, lean_object* v_indName_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Elab_Deriving_mkInstName(v_className_1451_, v_indName_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(lean_object* v_00_u03b1_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(v_00_u03b1_1471_, v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(lean_object* v_msgData_1481_, lean_object* v_macroStack_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1481_, v_macroStack_1482_, v___y_1487_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1491_, lean_object* v_macroStack_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_1491_, v_macroStack_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(lean_object* v_as_x27_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
if (lean_obj_tag(v_as_x27_1501_) == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_b_1502_);
return v___x_1510_;
}
else
{
lean_object* v_head_1511_; lean_object* v_tail_1512_; lean_object* v___x_1513_; 
v_head_1511_ = lean_ctor_get(v_as_x27_1501_, 0);
v_tail_1512_ = lean_ctor_get(v_as_x27_1501_, 1);
lean_inc(v_head_1511_);
v___x_1513_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_head_1511_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_array_push(v_b_1502_, v_a_1514_);
v_as_x27_1501_ = v_tail_1512_;
v_b_1502_ = v___x_1515_;
goto _start;
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_b_1502_);
v_a_1517_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1513_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1513_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg___boxed(lean_object* v_as_x27_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1525_, v_b_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v_as_x27_1525_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
if (lean_obj_tag(v_a_1535_) == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = l_List_reverse___redArg(v_a_1536_);
return v___x_1537_;
}
else
{
lean_object* v_head_1538_; lean_object* v_tail_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1548_; 
v_head_1538_ = lean_ctor_get(v_a_1535_, 0);
v_tail_1539_ = lean_ctor_get(v_a_1535_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_a_1535_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1541_ = v_a_1535_;
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_tail_1539_);
lean_inc(v_head_1538_);
lean_dec(v_a_1535_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = l_Lean_MessageData_ofName(v_head_1538_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v_a_1536_);
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_a_1536_);
v___x_1545_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v_a_1535_ = v_tail_1539_;
v_a_1536_ = v___x_1545_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1549_; double v___x_1550_; 
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_float_of_nat(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(lean_object* v_cls_1554_, lean_object* v_msg_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_ref_1561_; lean_object* v___x_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1608_; 
v_ref_1561_ = lean_ctor_get(v___y_1558_, 2);
v___x_1562_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1608_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1608_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v_traceState_1568_; lean_object* v_env_1569_; lean_object* v_nextMacroScope_1570_; lean_object* v_ngen_1571_; lean_object* v_auxDeclNGen_1572_; lean_object* v_cache_1573_; lean_object* v_recordedDeps_1574_; lean_object* v_messages_1575_; lean_object* v_infoState_1576_; lean_object* v_snapshotTasks_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1607_; 
v___x_1567_ = lean_st_ref_take(v___y_1559_);
v_traceState_1568_ = lean_ctor_get(v___x_1567_, 4);
v_env_1569_ = lean_ctor_get(v___x_1567_, 0);
v_nextMacroScope_1570_ = lean_ctor_get(v___x_1567_, 1);
v_ngen_1571_ = lean_ctor_get(v___x_1567_, 2);
v_auxDeclNGen_1572_ = lean_ctor_get(v___x_1567_, 3);
v_cache_1573_ = lean_ctor_get(v___x_1567_, 5);
v_recordedDeps_1574_ = lean_ctor_get(v___x_1567_, 6);
v_messages_1575_ = lean_ctor_get(v___x_1567_, 7);
v_infoState_1576_ = lean_ctor_get(v___x_1567_, 8);
v_snapshotTasks_1577_ = lean_ctor_get(v___x_1567_, 9);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1579_ = v___x_1567_;
v_isShared_1580_ = v_isSharedCheck_1607_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snapshotTasks_1577_);
lean_inc(v_infoState_1576_);
lean_inc(v_messages_1575_);
lean_inc(v_recordedDeps_1574_);
lean_inc(v_cache_1573_);
lean_inc(v_traceState_1568_);
lean_inc(v_auxDeclNGen_1572_);
lean_inc(v_ngen_1571_);
lean_inc(v_nextMacroScope_1570_);
lean_inc(v_env_1569_);
lean_dec(v___x_1567_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1607_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
uint64_t v_tid_1581_; lean_object* v_traces_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1606_; 
v_tid_1581_ = lean_ctor_get_uint64(v_traceState_1568_, sizeof(void*)*1);
v_traces_1582_ = lean_ctor_get(v_traceState_1568_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_traceState_1568_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1584_ = v_traceState_1568_;
v_isShared_1585_ = v_isSharedCheck_1606_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_traces_1582_);
lean_dec(v_traceState_1568_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1606_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; double v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0);
v___x_1589_ = 0;
v___x_1590_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1));
v___x_1591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1591_, 0, v_cls_1554_);
lean_ctor_set(v___x_1591_, 1, v___x_1587_);
lean_ctor_set(v___x_1591_, 2, v___x_1590_);
lean_ctor_set_float(v___x_1591_, sizeof(void*)*3, v___x_1588_);
lean_ctor_set_float(v___x_1591_, sizeof(void*)*3 + 8, v___x_1588_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*3 + 16, v___x_1589_);
v___x_1592_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2));
v___x_1593_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v_a_1563_);
lean_ctor_set(v___x_1593_, 2, v___x_1592_);
lean_inc(v_ref_1561_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_ref_1561_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_PersistentArray_push___redArg(v_traces_1582_, v___x_1594_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1595_);
v___x_1597_ = v___x_1584_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1595_);
lean_ctor_set_uint64(v_reuseFailAlloc_1605_, sizeof(void*)*1, v_tid_1581_);
v___x_1597_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v___x_1597_);
v___x_1599_ = v___x_1579_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_env_1569_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_nextMacroScope_1570_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_ngen_1571_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_auxDeclNGen_1572_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1604_, 5, v_cache_1573_);
lean_ctor_set(v_reuseFailAlloc_1604_, 6, v_recordedDeps_1574_);
lean_ctor_set(v_reuseFailAlloc_1604_, 7, v_messages_1575_);
lean_ctor_set(v_reuseFailAlloc_1604_, 8, v_infoState_1576_);
lean_ctor_set(v_reuseFailAlloc_1604_, 9, v_snapshotTasks_1577_);
v___x_1599_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_st_ref_put(v___y_1559_, v___x_1599_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1586_);
v___x_1602_ = v___x_1565_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1586_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___boxed(lean_object* v_cls_1609_, lean_object* v_msg_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1609_, v_msg_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(lean_object* v_fnPrefix_1618_, lean_object* v_a_1619_, lean_object* v_range_1620_, lean_object* v_b_1621_, lean_object* v_i_1622_){
_start:
{
lean_object* v_stop_1624_; lean_object* v_step_1625_; uint8_t v___x_1626_; 
v_stop_1624_ = lean_ctor_get(v_range_1620_, 1);
v_step_1625_ = lean_ctor_get(v_range_1620_, 2);
v___x_1626_ = lean_nat_dec_lt(v_i_1622_, v_stop_1624_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_dec(v_i_1622_);
lean_dec(v_a_1619_);
lean_dec_ref(v_fnPrefix_1618_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_b_1621_);
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0));
lean_inc_ref(v_fnPrefix_1618_);
v___x_1630_ = lean_string_append(v_fnPrefix_1618_, v___x_1629_);
v___x_1631_ = lean_nat_add(v_i_1622_, v___x_1628_);
v___x_1632_ = l_Nat_reprFast(v___x_1631_);
v___x_1633_ = lean_string_append(v___x_1630_, v___x_1632_);
lean_dec_ref(v___x_1632_);
v___x_1634_ = lean_box(0);
v___x_1635_ = l_Lean_Name_str___override(v___x_1634_, v___x_1633_);
lean_inc(v_a_1619_);
v___x_1636_ = l_Lean_Name_append(v_a_1619_, v___x_1635_);
v___x_1637_ = lean_array_push(v_b_1621_, v___x_1636_);
v___x_1638_ = lean_nat_add(v_i_1622_, v_step_1625_);
lean_dec(v_i_1622_);
v_b_1621_ = v___x_1637_;
v_i_1622_ = v___x_1638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___boxed(lean_object* v_fnPrefix_1640_, lean_object* v_a_1641_, lean_object* v_range_1642_, lean_object* v_b_1643_, lean_object* v_i_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1640_, v_a_1641_, v_range_1642_, v_b_1643_, v_i_1644_);
lean_dec_ref(v_range_1642_);
return v_res_1646_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__5(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__4));
v___x_1657_ = l_Lean_Name_append(v___x_1656_, v___x_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__7(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__6));
v___x_1660_ = l_Lean_stringToMessageData(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__9(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__8));
v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext(lean_object* v_className_1664_, lean_object* v_fnPrefix_1665_, lean_object* v_typeName_1666_, uint8_t v_supportsRec_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1675_; 
lean_inc(v_typeName_1666_);
v___x_1675_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_typeName_1666_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v_all_1677_; uint8_t v_isRec_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v_all_1677_ = lean_ctor_get(v_a_1676_, 3);
v_isRec_1678_ = lean_ctor_get_uint8(v_a_1676_, sizeof(void*)*6);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1681_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_all_1677_, v___x_1680_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1683_ = l_Lean_Elab_Deriving_mkInstName(v_className_1664_, v_typeName_1666_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1745_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1745_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1745_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1696_; lean_object* v_auxFunNames_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = l_List_lengthTR___redArg(v_all_1677_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_dec_eq(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v_a_1740_; 
v___x_1738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1679_);
lean_ctor_set(v___x_1738_, 1, v___x_1735_);
lean_ctor_set(v___x_1738_, 2, v___x_1736_);
lean_inc(v_a_1684_);
v___x_1739_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1665_, v_a_1684_, v___x_1738_, v___x_1680_, v___x_1679_);
lean_dec_ref_known(v___x_1738_, 3);
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1739_);
v_auxFunNames_1702_ = v_a_1740_;
v___y_1703_ = v_a_1668_;
v___y_1704_ = v_a_1669_;
v___y_1705_ = v_a_1670_;
v___y_1706_ = v_a_1671_;
v___y_1707_ = v_a_1672_;
v___y_1708_ = v_a_1673_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v___x_1735_);
v___x_1741_ = lean_box(0);
v___x_1742_ = l_Lean_Name_str___override(v___x_1741_, v_fnPrefix_1665_);
lean_inc(v_a_1684_);
v___x_1743_ = l_Lean_Name_append(v_a_1684_, v___x_1742_);
v___x_1744_ = lean_array_push(v___x_1680_, v___x_1743_);
v_auxFunNames_1702_ = v___x_1744_;
v___y_1703_ = v_a_1668_;
v___y_1704_ = v_a_1669_;
v___y_1705_ = v_a_1670_;
v___y_1706_ = v_a_1671_;
v___y_1707_ = v_a_1672_;
v___y_1708_ = v_a_1673_;
goto v___jp_1701_;
}
v___jp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1691_, 0, v_a_1684_);
lean_ctor_set(v___x_1691_, 1, v_a_1682_);
lean_ctor_set(v___x_1691_, 2, v___y_1689_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*3, v___y_1690_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1691_);
v___x_1693_ = v___x_1686_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
v___jp_1695_:
{
uint8_t v___x_1697_; 
v___x_1697_ = l_Lean_InductiveVal_isNested(v_a_1676_);
lean_dec(v_a_1676_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = lean_unsigned_to_nat(1u);
v___x_1699_ = lean_array_get_size(v_a_1682_);
v___x_1700_ = lean_nat_dec_lt(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
if (v_isRec_1678_ == 0)
{
v___y_1689_ = v___y_1696_;
v___y_1690_ = v_isRec_1678_;
goto v___jp_1688_;
}
else
{
if (v_supportsRec_1667_ == 0)
{
v___y_1689_ = v___y_1696_;
v___y_1690_ = v_isRec_1678_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v___y_1696_;
v___y_1690_ = v___x_1700_;
goto v___jp_1688_;
}
}
}
else
{
v___y_1689_ = v___y_1696_;
v___y_1690_ = v___x_1700_;
goto v___jp_1688_;
}
}
else
{
v___y_1689_ = v___y_1696_;
v___y_1690_ = v___x_1697_;
goto v___jp_1688_;
}
}
v___jp_1701_:
{
lean_object* v_toCold_1709_; lean_object* v_options_1710_; uint8_t v_hasTrace_1711_; 
v_toCold_1709_ = lean_ctor_get(v___y_1707_, 0);
v_options_1710_ = lean_ctor_get(v_toCold_1709_, 2);
v_hasTrace_1711_ = lean_ctor_get_uint8(v_options_1710_, sizeof(void*)*1);
if (v_hasTrace_1711_ == 0)
{
v___y_1696_ = v_auxFunNames_1702_;
goto v___jp_1695_;
}
else
{
lean_object* v_inheritedTraceOptions_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v_inheritedTraceOptions_1712_ = lean_ctor_get(v_toCold_1709_, 11);
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1714_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__5, &l_Lean_Elab_Deriving_mkContext___closed__5_once, _init_l_Lean_Elab_Deriving_mkContext___closed__5);
v___x_1715_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1712_, v_options_1710_, v___x_1714_);
if (v___x_1715_ == 0)
{
v___y_1696_ = v_auxFunNames_1702_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1716_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__7, &l_Lean_Elab_Deriving_mkContext___closed__7_once, _init_l_Lean_Elab_Deriving_mkContext___closed__7);
lean_inc(v_a_1684_);
v___x_1717_ = l_Lean_MessageData_ofName(v_a_1684_);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__9, &l_Lean_Elab_Deriving_mkContext___closed__9_once, _init_l_Lean_Elab_Deriving_mkContext___closed__9);
v___x_1720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_inc_ref(v_auxFunNames_1702_);
v___x_1721_ = lean_array_to_list(v_auxFunNames_1702_);
v___x_1722_ = lean_box(0);
v___x_1723_ = l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(v___x_1721_, v___x_1722_);
v___x_1724_ = l_Lean_MessageData_ofList(v___x_1723_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1720_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v___x_1713_, v___x_1725_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_dec_ref_known(v___x_1726_, 1);
v___y_1696_ = v_auxFunNames_1702_;
goto v___jp_1695_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v_auxFunNames_1702_);
lean_del_object(v___x_1686_);
lean_dec(v_a_1684_);
lean_dec(v_a_1682_);
lean_dec(v_a_1676_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
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
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1682_);
lean_dec(v_a_1676_);
lean_dec_ref(v_fnPrefix_1665_);
v_a_1746_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1683_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1683_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1676_);
lean_dec(v_typeName_1666_);
lean_dec_ref(v_fnPrefix_1665_);
lean_dec(v_className_1664_);
v_a_1754_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1681_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1681_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_typeName_1666_);
lean_dec_ref(v_fnPrefix_1665_);
lean_dec(v_className_1664_);
v_a_1762_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1675_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1675_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object* v_className_1770_, lean_object* v_fnPrefix_1771_, lean_object* v_typeName_1772_, lean_object* v_supportsRec_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
uint8_t v_supportsRec_boxed_1781_; lean_object* v_res_1782_; 
v_supportsRec_boxed_1781_ = lean_unbox(v_supportsRec_1773_);
v_res_1782_ = l_Lean_Elab_Deriving_mkContext(v_className_1770_, v_fnPrefix_1771_, v_typeName_1772_, v_supportsRec_boxed_1781_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(lean_object* v_as_1783_, lean_object* v_as_x27_1784_, lean_object* v_b_1785_, lean_object* v_a_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1784_, v_b_1785_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___boxed(lean_object* v_as_1795_, lean_object* v_as_x27_1796_, lean_object* v_b_1797_, lean_object* v_a_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(v_as_1795_, v_as_x27_1796_, v_b_1797_, v_a_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v_as_x27_1796_);
lean_dec(v_as_1795_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(lean_object* v_cls_1807_, lean_object* v_msg_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1807_, v_msg_1808_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___boxed(lean_object* v_cls_1817_, lean_object* v_msg_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(v_cls_1817_, v_msg_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(lean_object* v_fnPrefix_1827_, lean_object* v_a_1828_, lean_object* v_range_1829_, lean_object* v_b_1830_, lean_object* v_i_1831_, lean_object* v_hs_1832_, lean_object* v_hl_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1827_, v_a_1828_, v_range_1829_, v_b_1830_, v_i_1831_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(lean_object* v_fnPrefix_1842_, lean_object* v_a_1843_, lean_object* v_range_1844_, lean_object* v_b_1845_, lean_object* v_i_1846_, lean_object* v_hs_1847_, lean_object* v_hl_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_1842_, v_a_1843_, v_range_1844_, v_b_1845_, v_i_1846_, v_hs_1847_, v_hl_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec_ref(v_range_1844_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_1857_, lean_object* v_b_1858_){
_start:
{
lean_object* v_array_1859_; lean_object* v_start_1860_; lean_object* v_stop_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1874_; 
v_array_1859_ = lean_ctor_get(v_a_1857_, 0);
v_start_1860_ = lean_ctor_get(v_a_1857_, 1);
v_stop_1861_ = lean_ctor_get(v_a_1857_, 2);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_a_1857_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1863_ = v_a_1857_;
v_isShared_1864_ = v_isSharedCheck_1874_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_stop_1861_);
lean_inc(v_start_1860_);
lean_inc(v_array_1859_);
lean_dec(v_a_1857_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1874_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_nat_dec_lt(v_start_1860_, v_stop_1861_);
if (v___x_1865_ == 0)
{
lean_del_object(v___x_1863_);
lean_dec(v_stop_1861_);
lean_dec(v_start_1860_);
lean_dec_ref(v_array_1859_);
return v_b_1858_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_start_1860_, v___x_1866_);
lean_inc_ref(v_array_1859_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1867_);
v___x_1869_ = v___x_1863_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_array_1859_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_stop_1861_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_array_fget(v_array_1859_, v_start_1860_);
lean_dec(v_start_1860_);
lean_dec_ref(v_array_1859_);
v___x_1871_ = lean_array_push(v_b_1858_, v___x_1870_);
v_a_1857_ = v___x_1869_;
v_b_1858_ = v___x_1871_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_ref_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_ref_1882_ = lean_ctor_get(v___y_1879_, 2);
v___x_1883_ = 0;
v___x_1884_ = l_Lean_SourceInfo_fromRef(v_ref_1882_, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(lean_object* v_upperBound_1931_, lean_object* v___x_1932_, lean_object* v_ctx_1933_, lean_object* v_argNames_1934_, lean_object* v_className_1935_, lean_object* v_a_1936_, lean_object* v_b_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_lt(v_a_1936_, v_upperBound_1931_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_b_1937_);
return v___x_1946_;
}
else
{
lean_object* v_auxFunNames_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_auxFunNames_1947_ = lean_ctor_get(v_ctx_1933_, 2);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_array_fget_borrowed(v___x_1932_, v_a_1936_);
v___x_1950_ = lean_array_get_borrowed(v___x_1948_, v_auxFunNames_1947_, v_a_1936_);
lean_inc(v___x_1949_);
v___x_1951_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_1949_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_numParams_1953_; lean_object* v_lower_1955_; lean_object* v_upper_1956_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v_numParams_1953_ = lean_ctor_get(v___x_1949_, 1);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_array_get_size(v_a_1952_);
v___x_2050_ = lean_nat_dec_le(v_numParams_1953_, v___x_2048_);
if (v___x_2050_ == 0)
{
lean_inc(v_numParams_1953_);
v_lower_1955_ = v_numParams_1953_;
v_upper_1956_ = v___x_2049_;
goto v___jp_1954_;
}
else
{
v_lower_1955_ = v___x_2048_;
v_upper_1956_ = v___x_2049_;
goto v___jp_1954_;
}
v___jp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = l_Array_toSubarray___redArg(v_a_1952_, v_lower_1955_, v_upper_1956_);
lean_inc_ref(v___x_1957_);
v___x_1958_ = l_Subarray_copy___redArg(v___x_1957_);
v___x_1959_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_1958_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1953_);
lean_inc_ref(v_argNames_1934_);
v___x_1962_ = l_Array_toSubarray___redArg(v_argNames_1934_, v___x_1961_, v_numParams_1953_);
v___x_1963_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_1964_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1962_, v___x_1963_);
v___x_1965_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1957_, v___x_1963_);
v_a_1966_ = l_Array_append___redArg(v___x_1964_, v___x_1965_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = lean_array_get_size(v_a_1966_);
v___x_1968_ = l_Array_toSubarray___redArg(v_a_1966_, v___x_1961_, v___x_1967_);
v___x_1969_ = l_Subarray_copy___redArg(v___x_1968_);
lean_inc(v___x_1949_);
v___x_1970_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_1949_, v___x_1969_, v___y_1942_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v_ref_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v_ref_1972_ = lean_ctor_get(v___y_1942_, 2);
v___x_1973_ = 0;
v___x_1974_ = l_Lean_SourceInfo_fromRef(v_ref_1972_, v___x_1973_);
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_1935_);
v___x_1976_ = l_Lean_mkCIdent(v_className_1935_);
v___x_1977_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1974_);
v___x_1978_ = l_Lean_Syntax_node1(v___x_1974_, v___x_1977_, v_a_1971_);
v___x_1979_ = l_Lean_Syntax_node2(v___x_1974_, v___x_1975_, v___x_1976_, v___x_1978_);
v___x_1980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_n(v_a_1981_, 4);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1));
v___x_1983_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_1984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1981_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
lean_inc(v___x_1950_);
v___x_1985_ = l_Lean_mkIdent(v___x_1950_);
v___x_1986_ = l_Lean_Syntax_node1(v_a_1981_, v___x_1977_, v___x_1985_);
v___x_1987_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_1988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_a_1981_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_Syntax_node3(v_a_1981_, v___x_1982_, v___x_1984_, v___x_1986_, v___x_1988_);
v___x_1990_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5));
v___x_1991_ = l_Lean_Core_mkFreshUserName(v___x_1990_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc_n(v_a_1994_, 8);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7));
v___x_1996_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9));
v___x_1997_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11));
v___x_1998_ = l_Lean_mkIdent(v_a_1992_);
v___x_1999_ = l_Lean_Syntax_node1(v_a_1994_, v___x_1997_, v___x_1998_);
v___x_2000_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2001_ = l_Array_append___redArg(v___x_2000_, v_a_1960_);
lean_dec(v_a_1960_);
v___x_2002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2002_, 0, v_a_1994_);
lean_ctor_set(v___x_2002_, 1, v___x_1977_);
lean_ctor_set(v___x_2002_, 2, v___x_2001_);
v___x_2003_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13));
v___x_2004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_a_1994_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = l_Lean_Syntax_node2(v_a_1994_, v___x_2003_, v___x_2005_, v___x_1979_);
v___x_2007_ = l_Lean_Syntax_node1(v_a_1994_, v___x_1977_, v___x_2006_);
v___x_2008_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_2009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_a_1994_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Lean_Syntax_node5(v_a_1994_, v___x_1996_, v___x_1999_, v___x_2002_, v___x_2007_, v___x_2009_, v___x_1989_);
v___x_2011_ = l_Lean_Syntax_node1(v_a_1994_, v___x_1995_, v___x_2010_);
v___x_2012_ = lean_array_push(v_b_1937_, v___x_2011_);
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = lean_nat_add(v_a_1936_, v___x_2013_);
lean_dec(v_a_1936_);
v_a_1936_ = v___x_2014_;
v_b_1937_ = v___x_2012_;
goto _start;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_a_1992_);
lean_dec(v___x_1989_);
lean_dec(v___x_1979_);
lean_dec(v_a_1960_);
lean_dec_ref(v_b_1937_);
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
v_a_2016_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1993_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1993_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v___x_1989_);
lean_dec(v___x_1979_);
lean_dec(v_a_1960_);
lean_dec_ref(v_b_1937_);
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
v_a_2024_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1991_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1991_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v___x_1979_);
lean_dec(v_a_1960_);
lean_dec_ref(v_b_1937_);
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
v_a_2032_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1980_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1980_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_1960_);
lean_dec_ref(v_b_1937_);
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
v_a_2040_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1970_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1970_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_b_1937_);
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
return v___x_1959_;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_b_1937_);
lean_dec(v_a_1936_);
lean_dec(v_className_1935_);
lean_dec_ref(v_argNames_1934_);
v_a_2051_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1951_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1951_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___boxed(lean_object* v_upperBound_2059_, lean_object* v___x_2060_, lean_object* v_ctx_2061_, lean_object* v_argNames_2062_, lean_object* v_className_2063_, lean_object* v_a_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_2059_, v___x_2060_, v_ctx_2061_, v_argNames_2062_, v_className_2063_, v_a_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec_ref(v_ctx_2061_);
lean_dec_ref(v___x_2060_);
lean_dec(v_upperBound_2059_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object* v_ctx_2074_, lean_object* v_className_2075_, lean_object* v_argNames_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_typeInfos_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_letDecls_2087_; lean_object* v___x_2088_; 
v_typeInfos_2084_ = lean_ctor_get(v_ctx_2074_, 1);
v___x_2085_ = lean_array_get_size(v_typeInfos_2084_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v_letDecls_2087_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v___x_2085_, v_typeInfos_2084_, v_ctx_2074_, v_argNames_2076_, v_className_2075_, v___x_2086_, v_letDecls_2087_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2089_, lean_object* v_className_2090_, lean_object* v_argNames_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2089_, v_className_2090_, v_argNames_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec_ref(v_ctx_2089_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2100_, lean_object* v_R_2101_, lean_object* v_a_2102_, lean_object* v_b_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2102_, v_b_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(lean_object* v_upperBound_2105_, lean_object* v___x_2106_, lean_object* v_ctx_2107_, lean_object* v_argNames_2108_, lean_object* v_className_2109_, lean_object* v_inst_2110_, lean_object* v_R_2111_, lean_object* v_a_2112_, lean_object* v_b_2113_, lean_object* v_c_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_2105_, v___x_2106_, v_ctx_2107_, v_argNames_2108_, v_className_2109_, v_a_2112_, v_b_2113_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2123_ = _args[0];
lean_object* v___x_2124_ = _args[1];
lean_object* v_ctx_2125_ = _args[2];
lean_object* v_argNames_2126_ = _args[3];
lean_object* v_className_2127_ = _args[4];
lean_object* v_inst_2128_ = _args[5];
lean_object* v_R_2129_ = _args[6];
lean_object* v_a_2130_ = _args[7];
lean_object* v_b_2131_ = _args[8];
lean_object* v_c_2132_ = _args[9];
lean_object* v___y_2133_ = _args[10];
lean_object* v___y_2134_ = _args[11];
lean_object* v___y_2135_ = _args[12];
lean_object* v___y_2136_ = _args[13];
lean_object* v___y_2137_ = _args[14];
lean_object* v___y_2138_ = _args[15];
lean_object* v___y_2139_ = _args[16];
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(v_upperBound_2123_, v___x_2124_, v_ctx_2125_, v_argNames_2126_, v_className_2127_, v_inst_2128_, v_R_2129_, v_a_2130_, v_b_2131_, v_c_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_ctx_2125_);
lean_dec_ref(v___x_2124_);
lean_dec(v_upperBound_2123_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(lean_object* v_as_2154_, size_t v_i_2155_, size_t v_stop_2156_, lean_object* v_b_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_usize_dec_eq(v_i_2155_, v_stop_2156_);
if (v___x_2160_ == 0)
{
lean_object* v_ref_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_ref_2161_ = lean_ctor_get(v___y_2158_, 2);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_sub(v_i_2155_, v___x_2162_);
v___x_2164_ = lean_array_uget_borrowed(v_as_2154_, v___x_2163_);
v___x_2165_ = l_Lean_SourceInfo_fromRef(v_ref_2161_, v___x_2160_);
v___x_2166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0));
v___x_2167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1));
lean_inc_n(v___x_2165_, 4);
v___x_2168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2165_);
lean_ctor_set(v___x_2168_, 1, v___x_2166_);
v___x_2169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3));
v___x_2170_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2171_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2165_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
lean_ctor_set(v___x_2172_, 2, v___x_2171_);
v___x_2173_ = l_Lean_Syntax_node1(v___x_2165_, v___x_2169_, v___x_2172_);
v___x_2174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4));
v___x_2175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2165_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
lean_inc(v___x_2164_);
v___x_2176_ = l_Lean_Syntax_node5(v___x_2165_, v___x_2167_, v___x_2168_, v___x_2173_, v___x_2164_, v___x_2175_, v_b_2157_);
v_i_2155_ = v___x_2163_;
v_b_2157_ = v___x_2176_;
goto _start;
}
else
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_b_2157_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(lean_object* v_as_2179_, lean_object* v_i_2180_, lean_object* v_stop_2181_, lean_object* v_b_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
size_t v_i_boxed_2185_; size_t v_stop_boxed_2186_; lean_object* v_res_2187_; 
v_i_boxed_2185_ = lean_unbox_usize(v_i_2180_);
lean_dec(v_i_2180_);
v_stop_boxed_2186_ = lean_unbox_usize(v_stop_2181_);
lean_dec(v_stop_2181_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2179_, v_i_boxed_2185_, v_stop_boxed_2186_, v_b_2182_, v___y_2183_);
lean_dec_ref(v___y_2183_);
lean_dec_ref(v_as_2179_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet(lean_object* v_letDecls_2188_, lean_object* v_body_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2197_ = lean_array_get_size(v_letDecls_2188_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_nat_dec_lt(v___x_2198_, v___x_2197_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_body_2189_);
return v___x_2200_;
}
else
{
size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_usize_of_nat(v___x_2197_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_letDecls_2188_, v___x_2201_, v___x_2202_, v_body_2189_, v_a_2194_);
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet___boxed(lean_object* v_letDecls_2204_, lean_object* v_body_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Elab_Deriving_mkLet(v_letDecls_2204_, v_body_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_letDecls_2204_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(lean_object* v_as_2214_, size_t v_i_2215_, size_t v_stop_2216_, lean_object* v_b_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2214_, v_i_2215_, v_stop_2216_, v_b_2217_, v___y_2222_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(lean_object* v_as_2226_, lean_object* v_i_2227_, lean_object* v_stop_2228_, lean_object* v_b_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
size_t v_i_boxed_2237_; size_t v_stop_boxed_2238_; lean_object* v_res_2239_; 
v_i_boxed_2237_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_stop_boxed_2238_ = lean_unbox_usize(v_stop_2228_);
lean_dec(v_stop_2228_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_2226_, v_i_boxed_2237_, v_stop_boxed_2238_, v_b_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v_as_2226_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(lean_object* v_className_2249_, lean_object* v_name_2250_, lean_object* v___f_2251_, lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v_b_2258_, lean_object* v_____r_2259_, lean_object* v_val_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Elab_Deriving_mkInstName(v_className_2249_, v_name_2250_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
v___x_2270_ = lean_apply_7(v___f_2251_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, lean_box(0));
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2320_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2320_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2320_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0));
v___x_2276_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1));
lean_inc_ref_n(v___x_2253_, 8);
lean_inc_ref_n(v___x_2252_, 8);
v___x_2277_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2275_, v___x_2276_);
v___x_2278_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2));
v___x_2279_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2275_, v___x_2278_);
v___x_2280_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc_n(v___x_2254_, 2);
lean_inc_n(v_a_2271_, 14);
v___x_2281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2281_, 0, v_a_2271_);
lean_ctor_set(v___x_2281_, 1, v___x_2254_);
lean_ctor_set(v___x_2281_, 2, v___x_2280_);
lean_inc_ref_n(v___x_2281_, 12);
v___x_2282_ = l_Lean_Syntax_node7(v_a_2271_, v___x_2279_, v___x_2281_, v___x_2281_, v___x_2281_, v___x_2281_, v___x_2281_, v___x_2281_, v___x_2281_);
v___x_2283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3));
v___x_2284_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2275_, v___x_2283_);
v___x_2285_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2));
lean_inc_ref(v___x_2255_);
v___x_2286_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2255_, v___x_2285_);
v___x_2287_ = l_Lean_Syntax_node1(v_a_2271_, v___x_2286_, v___x_2281_);
v___x_2288_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_a_2271_);
lean_ctor_set(v___x_2288_, 1, v___x_2283_);
v___x_2289_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4));
v___x_2290_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2275_, v___x_2289_);
v___x_2291_ = l_Lean_mkIdent(v_a_2269_);
v___x_2292_ = l_Lean_Syntax_node2(v_a_2271_, v___x_2290_, v___x_2291_, v___x_2281_);
v___x_2293_ = l_Lean_Syntax_node1(v_a_2271_, v___x_2254_, v___x_2292_);
v___x_2294_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5));
v___x_2295_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2275_, v___x_2294_);
v___x_2296_ = l_Array_append___redArg(v___x_2280_, v___x_2256_);
v___x_2297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2297_, 0, v_a_2271_);
lean_ctor_set(v___x_2297_, 1, v___x_2254_);
lean_ctor_set(v___x_2297_, 2, v___x_2296_);
v___x_2298_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12));
v___x_2299_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2255_, v___x_2298_);
v___x_2300_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2271_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_Syntax_node2(v_a_2271_, v___x_2299_, v___x_2301_, v___x_2257_);
v___x_2303_ = l_Lean_Syntax_node2(v_a_2271_, v___x_2295_, v___x_2297_, v___x_2302_);
v___x_2304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6));
v___x_2305_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2275_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_2307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_a_2271_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7));
v___x_2309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8));
v___x_2310_ = l_Lean_Name_mkStr4(v___x_2252_, v___x_2253_, v___x_2308_, v___x_2309_);
v___x_2311_ = l_Lean_Syntax_node2(v_a_2271_, v___x_2310_, v___x_2281_, v___x_2281_);
v___x_2312_ = l_Lean_Syntax_node4(v_a_2271_, v___x_2305_, v___x_2307_, v_val_2260_, v___x_2311_, v___x_2281_);
v___x_2313_ = l_Lean_Syntax_node6(v_a_2271_, v___x_2284_, v___x_2287_, v___x_2288_, v___x_2281_, v___x_2293_, v___x_2303_, v___x_2312_);
v___x_2314_ = l_Lean_Syntax_node2(v_a_2271_, v___x_2277_, v___x_2282_, v___x_2313_);
v___x_2315_ = lean_array_push(v_b_2258_, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2316_);
v___x_2318_ = v___x_2273_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2269_);
lean_dec(v_val_2260_);
lean_dec_ref(v_b_2258_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2255_);
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
v_a_2321_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2270_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2270_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v_val_2260_);
lean_dec_ref(v_b_2258_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2255_);
lean_dec(v___x_2254_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___x_2252_);
lean_dec_ref(v___f_2251_);
v_a_2329_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2268_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2268_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_className_2337_ = _args[0];
lean_object* v_name_2338_ = _args[1];
lean_object* v___f_2339_ = _args[2];
lean_object* v___x_2340_ = _args[3];
lean_object* v___x_2341_ = _args[4];
lean_object* v___x_2342_ = _args[5];
lean_object* v___x_2343_ = _args[6];
lean_object* v___x_2344_ = _args[7];
lean_object* v___x_2345_ = _args[8];
lean_object* v_b_2346_ = _args[9];
lean_object* v_____r_2347_ = _args[10];
lean_object* v_val_2348_ = _args[11];
lean_object* v___y_2349_ = _args[12];
lean_object* v___y_2350_ = _args[13];
lean_object* v___y_2351_ = _args[14];
lean_object* v___y_2352_ = _args[15];
lean_object* v___y_2353_ = _args[16];
lean_object* v___y_2354_ = _args[17];
lean_object* v___y_2355_ = _args[18];
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v_className_2337_, v_name_2338_, v___f_2339_, v___x_2340_, v___x_2341_, v___x_2342_, v___x_2343_, v___x_2344_, v___x_2345_, v_b_2346_, v_____r_2347_, v_val_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v___x_2344_);
return v_res_2356_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_2357_, lean_object* v_as_2358_, size_t v_i_2359_, size_t v_stop_2360_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_usize_dec_eq(v_i_2359_, v_stop_2360_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = lean_array_uget_borrowed(v_as_2358_, v_i_2359_);
v___x_2363_ = lean_name_eq(v_a_2357_, v___x_2362_);
if (v___x_2363_ == 0)
{
size_t v___x_2364_; size_t v___x_2365_; 
v___x_2364_ = ((size_t)1ULL);
v___x_2365_ = lean_usize_add(v_i_2359_, v___x_2364_);
v_i_2359_ = v___x_2365_;
goto _start;
}
else
{
return v___x_2363_;
}
}
else
{
uint8_t v___x_2367_; 
v___x_2367_ = 0;
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_2368_, lean_object* v_as_2369_, lean_object* v_i_2370_, lean_object* v_stop_2371_){
_start:
{
size_t v_i_boxed_2372_; size_t v_stop_boxed_2373_; uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_i_boxed_2372_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_stop_boxed_2373_ = lean_unbox_usize(v_stop_2371_);
lean_dec(v_stop_2371_);
v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2368_, v_as_2369_, v_i_boxed_2372_, v_stop_boxed_2373_);
lean_dec_ref(v_as_2369_);
lean_dec(v_a_2368_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(lean_object* v_as_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_array_get_size(v_as_2376_);
v___x_2380_ = lean_nat_dec_lt(v___x_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
return v___x_2380_;
}
else
{
size_t v___x_2381_; size_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = ((size_t)0ULL);
v___x_2382_ = lean_usize_of_nat(v___x_2379_);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2377_, v_as_2376_, v___x_2381_, v___x_2382_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0___boxed(lean_object* v_as_2384_, lean_object* v_a_2385_){
_start:
{
uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_res_2386_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_as_2384_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(lean_object* v_upperBound_2389_, lean_object* v___x_2390_, lean_object* v_typeNames_2391_, lean_object* v_ctx_2392_, lean_object* v_className_2393_, uint8_t v_useAnonCtor_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_a_2405_; lean_object* v___y_2410_; uint8_t v___x_2429_; 
v___x_2429_ = lean_nat_dec_lt(v_a_2395_, v_upperBound_2389_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_b_2396_);
return v___x_2430_;
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_toConstantVal_2433_; lean_object* v_name_2434_; uint8_t v___x_2435_; 
v___x_2431_ = l_Lean_instInhabitedInductiveVal_default;
v___x_2432_ = lean_array_get_borrowed(v___x_2431_, v___x_2390_, v_a_2395_);
v_toConstantVal_2433_ = lean_ctor_get(v___x_2432_, 0);
v_name_2434_ = lean_ctor_get(v_toConstantVal_2433_, 0);
v___x_2435_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_typeNames_2391_, v_name_2434_);
if (v___x_2435_ == 0)
{
v_a_2405_ = v_b_2396_;
goto v___jp_2404_;
}
else
{
lean_object* v_auxFunNames_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_auxFunNames_2436_ = lean_ctor_get(v_ctx_2392_, 2);
v___f_2437_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0));
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_array_get_borrowed(v___x_2438_, v_auxFunNames_2436_, v_a_2395_);
lean_inc(v___x_2432_);
v___x_2440_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_2432_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc_n(v_a_2441_, 2);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2441_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
lean_inc(v_a_2441_);
lean_inc(v___x_2432_);
lean_inc(v_className_2393_);
v___x_2444_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2393_, v___x_2432_, v_a_2441_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0));
v___x_2447_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1));
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2));
v___x_2449_ = l_Array_append___redArg(v_a_2443_, v_a_2445_);
lean_dec(v_a_2445_);
lean_inc(v___x_2432_);
v___x_2450_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_2432_, v_a_2441_, v___y_2401_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v_ref_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_ref_2452_ = lean_ctor_get(v___y_2401_, 2);
v___x_2453_ = 0;
v___x_2454_ = l_Lean_SourceInfo_fromRef(v_ref_2452_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_2393_);
v___x_2456_ = l_Lean_mkCIdent(v_className_2393_);
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_2454_);
v___x_2458_ = l_Lean_Syntax_node1(v___x_2454_, v___x_2457_, v_a_2451_);
v___x_2459_ = l_Lean_Syntax_node2(v___x_2454_, v___x_2455_, v___x_2456_, v___x_2458_);
lean_inc(v___x_2439_);
v___x_2460_ = l_Lean_mkIdent(v___x_2439_);
if (v_useAnonCtor_2394_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_box(0);
lean_inc(v_name_2434_);
lean_inc(v_className_2393_);
v___x_2462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v_className_2393_, v_name_2434_, v___f_2437_, v___x_2446_, v___x_2447_, v___x_2457_, v___x_2448_, v___x_2449_, v___x_2459_, v_b_2396_, v___x_2461_, v___x_2460_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v___x_2449_);
v___y_2410_ = v___x_2462_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_n(v_a_2464_, 4);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1));
v___x_2466_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_2467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2464_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_node1(v_a_2464_, v___x_2457_, v___x_2460_);
v___x_2469_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2464_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l_Lean_Syntax_node3(v_a_2464_, v___x_2465_, v___x_2467_, v___x_2468_, v___x_2470_);
v___x_2472_ = lean_box(0);
lean_inc(v_name_2434_);
lean_inc(v_className_2393_);
v___x_2473_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v_className_2393_, v_name_2434_, v___f_2437_, v___x_2446_, v___x_2447_, v___x_2457_, v___x_2448_, v___x_2449_, v___x_2459_, v_b_2396_, v___x_2472_, v___x_2471_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v___x_2449_);
v___y_2410_ = v___x_2473_;
goto v___jp_2409_;
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___x_2460_);
lean_dec(v___x_2459_);
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_b_2396_);
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v_a_2474_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2463_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2463_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_b_2396_);
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v_a_2482_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2450_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2450_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_a_2443_);
lean_dec(v_a_2441_);
lean_dec_ref(v_b_2396_);
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v_a_2490_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2444_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2444_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_dec(v_a_2441_);
lean_dec_ref(v_b_2396_);
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
return v___x_2442_;
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref(v_b_2396_);
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v_a_2498_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2440_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2440_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
v___jp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_add(v_a_2395_, v___x_2406_);
lean_dec(v_a_2395_);
v_a_2395_ = v___x_2407_;
v_b_2396_ = v_a_2405_;
goto _start;
}
v___jp_2409_:
{
if (lean_obj_tag(v___y_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2420_; 
v_a_2411_ = lean_ctor_get(v___y_2410_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___y_2410_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2413_ = v___y_2410_;
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___y_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
if (lean_obj_tag(v_a_2411_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; 
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v_a_2415_ = lean_ctor_get(v_a_2411_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v_a_2411_, 1);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v_a_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
else
{
lean_object* v_a_2419_; 
lean_del_object(v___x_2413_);
v_a_2419_ = lean_ctor_get(v_a_2411_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v_a_2411_, 1);
v_a_2405_ = v_a_2419_;
goto v___jp_2404_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_a_2395_);
lean_dec(v_className_2393_);
v_a_2421_ = lean_ctor_get(v___y_2410_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___y_2410_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___y_2410_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___y_2410_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_upperBound_2506_, lean_object* v___x_2507_, lean_object* v_typeNames_2508_, lean_object* v_ctx_2509_, lean_object* v_className_2510_, lean_object* v_useAnonCtor_2511_, lean_object* v_a_2512_, lean_object* v_b_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
uint8_t v_useAnonCtor_boxed_2521_; lean_object* v_res_2522_; 
v_useAnonCtor_boxed_2521_ = lean_unbox(v_useAnonCtor_2511_);
v_res_2522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2506_, v___x_2507_, v_typeNames_2508_, v_ctx_2509_, v_className_2510_, v_useAnonCtor_boxed_2521_, v_a_2512_, v_b_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_ctx_2509_);
lean_dec_ref(v_typeNames_2508_);
lean_dec_ref(v___x_2507_);
lean_dec(v_upperBound_2506_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object* v_ctx_2523_, lean_object* v_className_2524_, lean_object* v_typeNames_2525_, uint8_t v_useAnonCtor_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_typeInfos_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_instances_2537_; lean_object* v___x_2538_; 
v_typeInfos_2534_ = lean_ctor_get(v_ctx_2523_, 1);
v___x_2535_ = lean_array_get_size(v_typeInfos_2534_);
v___x_2536_ = lean_unsigned_to_nat(0u);
v_instances_2537_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v___x_2535_, v_typeInfos_2534_, v_typeNames_2525_, v_ctx_2523_, v_className_2524_, v_useAnonCtor_2526_, v___x_2536_, v_instances_2537_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds___boxed(lean_object* v_ctx_2539_, lean_object* v_className_2540_, lean_object* v_typeNames_2541_, lean_object* v_useAnonCtor_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
uint8_t v_useAnonCtor_boxed_2550_; lean_object* v_res_2551_; 
v_useAnonCtor_boxed_2550_ = lean_unbox(v_useAnonCtor_2542_);
v_res_2551_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_2539_, v_className_2540_, v_typeNames_2541_, v_useAnonCtor_boxed_2550_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_typeNames_2541_);
lean_dec_ref(v_ctx_2539_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(lean_object* v_upperBound_2552_, lean_object* v___x_2553_, lean_object* v_typeNames_2554_, lean_object* v_ctx_2555_, lean_object* v_className_2556_, uint8_t v_useAnonCtor_2557_, lean_object* v_inst_2558_, lean_object* v_R_2559_, lean_object* v_a_2560_, lean_object* v_b_2561_, lean_object* v_c_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2552_, v___x_2553_, v_typeNames_2554_, v_ctx_2555_, v_className_2556_, v_useAnonCtor_2557_, v_a_2560_, v_b_2561_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2571_ = _args[0];
lean_object* v___x_2572_ = _args[1];
lean_object* v_typeNames_2573_ = _args[2];
lean_object* v_ctx_2574_ = _args[3];
lean_object* v_className_2575_ = _args[4];
lean_object* v_useAnonCtor_2576_ = _args[5];
lean_object* v_inst_2577_ = _args[6];
lean_object* v_R_2578_ = _args[7];
lean_object* v_a_2579_ = _args[8];
lean_object* v_b_2580_ = _args[9];
lean_object* v_c_2581_ = _args[10];
lean_object* v___y_2582_ = _args[11];
lean_object* v___y_2583_ = _args[12];
lean_object* v___y_2584_ = _args[13];
lean_object* v___y_2585_ = _args[14];
lean_object* v___y_2586_ = _args[15];
lean_object* v___y_2587_ = _args[16];
lean_object* v___y_2588_ = _args[17];
_start:
{
uint8_t v_useAnonCtor_boxed_2589_; lean_object* v_res_2590_; 
v_useAnonCtor_boxed_2589_ = lean_unbox(v_useAnonCtor_2576_);
v_res_2590_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(v_upperBound_2571_, v___x_2572_, v_typeNames_2573_, v_ctx_2574_, v_className_2575_, v_useAnonCtor_boxed_2589_, v_inst_2577_, v_R_2578_, v_a_2579_, v_b_2580_, v_c_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v_ctx_2574_);
lean_dec_ref(v_typeNames_2573_);
lean_dec_ref(v___x_2572_);
lean_dec(v_upperBound_2571_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0_spec__1(lean_object* v_msgData_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v_toCold_2596_; lean_object* v_env_2597_; lean_object* v_options_2598_; uint8_t v___x_2599_; lean_object* v_env_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2595_ = lean_st_ref_get(v___y_2593_);
v_toCold_2596_ = lean_ctor_get(v___y_2592_, 0);
v_env_2597_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_ref(v_env_2597_);
lean_dec(v___x_2595_);
v_options_2598_ = lean_ctor_get(v_toCold_2596_, 2);
v___x_2599_ = 0;
v_env_2600_ = l_Lean_Environment_setRecordingDeps(v_env_2597_, v___x_2599_);
v___x_2601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2);
v___x_2602_ = lean_unsigned_to_nat(32u);
v___x_2603_ = lean_mk_empty_array_with_capacity(v___x_2602_);
lean_dec_ref(v___x_2603_);
v___x_2604_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2598_);
v___x_2605_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2605_, 0, v_env_2600_);
lean_ctor_set(v___x_2605_, 1, v___x_2601_);
lean_ctor_set(v___x_2605_, 2, v___x_2604_);
lean_ctor_set(v___x_2605_, 3, v_options_2598_);
v___x_2606_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v_msgData_2591_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0_spec__1(v_msgData_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg(lean_object* v_msg_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_ref_2617_; lean_object* v___x_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_ref_2617_ = lean_ctor_get(v___y_2614_, 2);
v___x_2618_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0_spec__1(v_msg_2613_, v___y_2614_, v___y_2615_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_inc(v_ref_2617_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_ref_2617_);
lean_ctor_set(v___x_2623_, 1, v_a_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 1);
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg(v_msg_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0(lean_object* v_constName_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v_env_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_st_ref_get(v___y_2635_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
lean_inc(v_constName_2633_);
v___x_2639_ = l_Lean_isInductiveCore_x3f(v_env_2638_, v_constName_2633_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2640_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_2641_ = 0;
v___x_2642_ = l_Lean_MessageData_ofConstName(v_constName_2633_, v___x_2641_);
v___x_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2640_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg(v___x_2645_, v___y_2634_, v___y_2635_);
return v___x_2646_;
}
else
{
lean_object* v_val_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_constName_2633_);
v_val_2647_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2639_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_val_2647_);
lean_dec(v___x_2639_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set_tag(v___x_2649_, 0);
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_val_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0___boxed(lean_object* v_constName_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0(v_constName_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__1(lean_object* v_as_2660_, size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_a_2668_; uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2662_, v_sz_2661_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_b_2663_);
return v___x_2673_;
}
else
{
lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2714_; 
v_fst_2674_ = lean_ctor_get(v_b_2663_, 0);
v_snd_2675_ = lean_ctor_get(v_b_2663_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_b_2663_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2677_ = v_b_2663_;
v_isShared_2678_ = v_isSharedCheck_2714_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_snd_2675_);
lean_inc(v_fst_2674_);
lean_dec(v_b_2663_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2714_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v_a_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_box(0);
v_a_2680_ = lean_array_uget_borrowed(v_as_2660_, v_i_2662_);
lean_inc(v_a_2680_);
v___x_2681_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0(v_a_2680_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___y_2684_; lean_object* v_all_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v_all_2688_ = lean_ctor_get(v_a_2682_, 3);
lean_inc(v_all_2688_);
lean_dec(v_a_2682_);
v___x_2689_ = l_List_head_x21___redArg(v___x_2679_, v_all_2688_);
lean_dec(v_all_2688_);
v___x_2690_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2675_, v___x_2689_);
if (lean_obj_tag(v___x_2690_) == 1)
{
lean_object* v_val_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
lean_dec(v___x_2689_);
v_val_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2692_ = lean_array_get_size(v_fst_2674_);
v___x_2693_ = lean_nat_dec_lt(v_val_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_dec(v_val_2691_);
v___y_2684_ = v_fst_2674_;
goto v___jp_2683_;
}
else
{
lean_object* v_v_2694_; lean_object* v___x_2695_; lean_object* v_xs_x27_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_v_2694_ = lean_array_fget(v_fst_2674_, v_val_2691_);
v___x_2695_ = lean_box(0);
v_xs_x27_2696_ = lean_array_fset(v_fst_2674_, v_val_2691_, v___x_2695_);
lean_inc(v_a_2680_);
v___x_2697_ = lean_array_push(v_v_2694_, v_a_2680_);
v___x_2698_ = lean_array_fset(v_xs_x27_2696_, v_val_2691_, v___x_2697_);
lean_dec(v_val_2691_);
v___y_2684_ = v___x_2698_;
goto v___jp_2683_;
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec(v___x_2690_);
lean_del_object(v___x_2677_);
v___x_2699_ = lean_array_get_size(v_fst_2674_);
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2689_, v___x_2699_, v_snd_2675_);
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
lean_inc(v_a_2680_);
v___x_2703_ = lean_array_push(v___x_2702_, v_a_2680_);
v___x_2704_ = lean_array_push(v_fst_2674_, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2700_);
v_a_2668_ = v___x_2705_;
goto v___jp_2667_;
}
v___jp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___y_2684_);
v___x_2686_ = v___x_2677_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___y_2684_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_snd_2675_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
v_a_2668_ = v___x_2686_;
goto v___jp_2667_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2677_);
lean_dec(v_snd_2675_);
lean_dec(v_fst_2674_);
v_a_2706_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2681_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2681_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
v___jp_2667_:
{
size_t v___x_2669_; size_t v___x_2670_; 
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_i_2662_, v___x_2669_);
v_i_2662_ = v___x_2670_;
v_b_2663_ = v_a_2668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__1___boxed(lean_object* v_as_2715_, lean_object* v_sz_2716_, lean_object* v_i_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
size_t v_sz_boxed_2722_; size_t v_i_boxed_2723_; lean_object* v_res_2724_; 
v_sz_boxed_2722_ = lean_unbox_usize(v_sz_2716_);
lean_dec(v_sz_2716_);
v_i_boxed_2723_ = lean_unbox_usize(v_i_2717_);
lean_dec(v_i_2717_);
v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__1(v_as_2715_, v_sz_boxed_2722_, v_i_boxed_2723_, v_b_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v_as_2715_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_groupByMutualBlock(lean_object* v_declNames_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v___x_2734_; size_t v_sz_2735_; size_t v___x_2736_; lean_object* v___x_2737_; 
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Deriving_groupByMutualBlock___closed__1));
v_sz_2735_ = lean_array_size(v_declNames_2730_);
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__1(v_declNames_2730_, v_sz_2735_, v___x_2736_, v___x_2734_, v_a_2731_, v_a_2732_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2746_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2746_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2746_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v_fst_2742_; lean_object* v___x_2744_; 
v_fst_2742_ = lean_ctor_get(v_a_2738_, 0);
lean_inc(v_fst_2742_);
lean_dec(v_a_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_fst_2742_);
v___x_2744_ = v___x_2740_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_fst_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_a_2747_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2737_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2737_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_groupByMutualBlock___boxed(lean_object* v_declNames_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Elab_Deriving_groupByMutualBlock(v_declNames_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec_ref(v_declNames_2755_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0(lean_object* v_00_u03b1_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___redArg(v_msg_2761_, v___y_2762_, v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_msg_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_groupByMutualBlock_spec__0_spec__0(v_00_u03b1_2766_, v_msg_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg(lean_object* v_varName_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_ref_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_ref_2781_ = lean_ctor_get(v_a_2779_, 2);
v___x_2782_ = 0;
v___x_2783_ = l_Lean_SourceInfo_fromRef(v_ref_2781_, v___x_2782_);
v___x_2784_ = ((lean_object*)(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1));
v___x_2785_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2786_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc(v___x_2783_);
v___x_2787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2783_);
lean_ctor_set(v___x_2787_, 1, v___x_2785_);
lean_ctor_set(v___x_2787_, 2, v___x_2786_);
v___x_2788_ = l_Lean_mkIdent(v_varName_2778_);
v___x_2789_ = l_Lean_Syntax_node2(v___x_2783_, v___x_2784_, v___x_2787_, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(lean_object* v_varName_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2791_, v_a_2792_);
lean_dec_ref(v_a_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr(lean_object* v_varName_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2795_, v_a_2800_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___boxed(lean_object* v_varName_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_Elab_Deriving_mkDiscr(v_varName_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(lean_object* v_upperBound_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_nat_dec_lt(v_a_2817_, v_upperBound_2816_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
lean_dec(v_a_2817_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v_b_2818_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1));
v___x_2825_ = l_Lean_Core_mkFreshUserName(v___x_2824_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = lean_array_push(v_b_2818_, v_a_2826_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_add(v_a_2817_, v___x_2828_);
lean_dec(v_a_2817_);
v_a_2817_ = v___x_2829_;
v_b_2818_ = v___x_2827_;
goto _start;
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v_b_2818_);
lean_dec(v_a_2817_);
v_a_2831_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2825_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2825_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___boxed(lean_object* v_upperBound_2839_, lean_object* v_a_2840_, lean_object* v_b_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2839_, v_a_2840_, v_b_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v_upperBound_2839_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(lean_object* v_a_2854_, size_t v_sz_2855_, size_t v_i_2856_, lean_object* v_bs_2857_, lean_object* v___y_2858_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_usize_dec_lt(v_i_2856_, v_sz_2855_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
lean_dec(v_a_2854_);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_bs_2857_);
return v___x_2861_;
}
else
{
lean_object* v_ref_2862_; lean_object* v_v_2863_; lean_object* v___x_2864_; lean_object* v_bs_x27_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; size_t v___x_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v_ref_2862_ = lean_ctor_get(v___y_2858_, 2);
v_v_2863_ = lean_array_uget(v_bs_2857_, v_i_2856_);
v___x_2864_ = lean_unsigned_to_nat(0u);
v_bs_x27_2865_ = lean_array_uset(v_bs_2857_, v_i_2856_, v___x_2864_);
v___x_2866_ = 0;
v___x_2867_ = l_Lean_SourceInfo_fromRef(v_ref_2862_, v___x_2866_);
v___x_2868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1));
v___x_2869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2));
lean_inc_n(v___x_2867_, 6);
v___x_2870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2867_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2872_ = l_Lean_mkIdent(v_v_2863_);
v___x_2873_ = l_Lean_Syntax_node1(v___x_2867_, v___x_2871_, v___x_2872_);
v___x_2874_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2867_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
lean_inc(v_a_2854_);
v___x_2876_ = l_Lean_Syntax_node2(v___x_2867_, v___x_2871_, v___x_2875_, v_a_2854_);
v___x_2877_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2867_);
lean_ctor_set(v___x_2878_, 1, v___x_2871_);
lean_ctor_set(v___x_2878_, 2, v___x_2877_);
v___x_2879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3));
v___x_2880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2867_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = l_Lean_Syntax_node5(v___x_2867_, v___x_2868_, v___x_2870_, v___x_2873_, v___x_2876_, v___x_2878_, v___x_2880_);
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_add(v_i_2856_, v___x_2882_);
v___x_2884_ = lean_array_uset(v_bs_x27_2865_, v_i_2856_, v___x_2881_);
v_i_2856_ = v___x_2883_;
v_bs_2857_ = v___x_2884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___boxed(lean_object* v_a_2886_, lean_object* v_sz_2887_, lean_object* v_i_2888_, lean_object* v_bs_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
size_t v_sz_boxed_2892_; size_t v_i_boxed_2893_; lean_object* v_res_2894_; 
v_sz_boxed_2892_ = lean_unbox_usize(v_sz_2887_);
lean_dec(v_sz_2887_);
v_i_boxed_2893_ = lean_unbox_usize(v_i_2888_);
lean_dec(v_i_2888_);
v_res_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2886_, v_sz_boxed_2892_, v_i_boxed_2893_, v_bs_2889_, v___y_2890_);
lean_dec_ref(v___y_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object* v_className_2895_, lean_object* v_arity_2896_, lean_object* v_indVal_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v___x_2905_; 
lean_inc_ref(v_indVal_2897_);
v___x_2905_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_n(v_a_2906_, 2);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2906_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
lean_inc(v_a_2906_);
lean_inc_ref(v_indVal_2897_);
v___x_2909_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_2897_, v_a_2906_, v_a_2902_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = lean_unsigned_to_nat(0u);
v___x_2912_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_2913_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_arity_2896_, v___x_2911_, v___x_2912_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
lean_inc(v_a_2906_);
v___x_2915_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2895_, v_indVal_2897_, v_a_2906_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; size_t v_sz_2918_; size_t v___x_2919_; lean_object* v___x_2920_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = l_Array_append___redArg(v_a_2908_, v_a_2916_);
lean_dec(v_a_2916_);
v_sz_2918_ = lean_array_size(v_a_2914_);
v___x_2919_ = ((size_t)0ULL);
lean_inc(v_a_2914_);
lean_inc(v_a_2910_);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2910_, v_sz_2918_, v___x_2919_, v_a_2914_, v_a_2902_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2930_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2923_ = v___x_2920_;
v_isShared_2924_ = v_isSharedCheck_2930_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2920_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2930_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2925_ = l_Array_append___redArg(v___x_2917_, v_a_2921_);
lean_dec(v_a_2921_);
v___x_2926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v_a_2906_);
lean_ctor_set(v___x_2926_, 2, v_a_2914_);
lean_ctor_set(v___x_2926_, 3, v_a_2910_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___x_2926_);
v___x_2928_ = v___x_2923_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v___x_2917_);
lean_dec(v_a_2914_);
lean_dec(v_a_2910_);
lean_dec(v_a_2906_);
v_a_2931_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2920_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2920_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_a_2914_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2906_);
v_a_2939_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2915_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2915_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2906_);
lean_dec_ref(v_indVal_2897_);
lean_dec(v_className_2895_);
v_a_2947_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2913_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2913_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2906_);
lean_dec_ref(v_indVal_2897_);
lean_dec(v_className_2895_);
v_a_2955_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2907_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2907_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_indVal_2897_);
lean_dec(v_className_2895_);
v_a_2963_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2905_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2905_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader___boxed(lean_object* v_className_2971_, lean_object* v_arity_2972_, lean_object* v_indVal_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Elab_Deriving_mkHeader(v_className_2971_, v_arity_2972_, v_indVal_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_arity_2972_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(lean_object* v_a_2982_, size_t v_sz_2983_, size_t v_i_2984_, lean_object* v_bs_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2982_, v_sz_2983_, v_i_2984_, v_bs_2985_, v___y_2990_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(lean_object* v_a_2994_, lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_bs_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
size_t v_sz_boxed_3005_; size_t v_i_boxed_3006_; lean_object* v_res_3007_; 
v_sz_boxed_3005_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_3006_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_2994_, v_sz_boxed_3005_, v_i_boxed_3006_, v_bs_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(lean_object* v_upperBound_3008_, lean_object* v_inst_3009_, lean_object* v_R_3010_, lean_object* v_a_3011_, lean_object* v_b_3012_, lean_object* v_c_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_3008_, v_a_3011_, v_b_3012_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___boxed(lean_object* v_upperBound_3022_, lean_object* v_inst_3023_, lean_object* v_R_3024_, lean_object* v_a_3025_, lean_object* v_b_3026_, lean_object* v_c_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(v_upperBound_3022_, v_inst_3023_, v_R_3024_, v_a_3025_, v_b_3026_, v_c_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v_upperBound_3022_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(lean_object* v_a_3036_, lean_object* v_b_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_array_3040_; lean_object* v_start_3041_; lean_object* v_stop_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3066_; 
v_array_3040_ = lean_ctor_get(v_a_3036_, 0);
v_start_3041_ = lean_ctor_get(v_a_3036_, 1);
v_stop_3042_ = lean_ctor_get(v_a_3036_, 2);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3044_ = v_a_3036_;
v_isShared_3045_ = v_isSharedCheck_3066_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_stop_3042_);
lean_inc(v_start_3041_);
lean_inc(v_array_3040_);
lean_dec(v_a_3036_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3066_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_lt(v_start_3041_, v_stop_3042_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
lean_del_object(v___x_3044_);
lean_dec(v_stop_3042_);
lean_dec(v_start_3041_);
lean_dec_ref(v_array_3040_);
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_b_3037_);
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = lean_unsigned_to_nat(1u);
v___x_3049_ = lean_nat_add(v_start_3041_, v___x_3048_);
lean_inc_ref(v_array_3040_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___x_3049_);
v___x_3051_ = v___x_3044_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_array_3040_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_stop_3042_);
v___x_3051_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_array_fget(v_array_3040_, v_start_3041_);
lean_dec(v_start_3041_);
lean_dec_ref(v_array_3040_);
v___x_3053_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v___x_3052_, v___y_3038_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = lean_array_push(v_b_3037_, v_a_3054_);
v_a_3036_ = v___x_3051_;
v_b_3037_ = v___x_3055_;
goto _start;
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___x_3051_);
lean_dec_ref(v_b_3037_);
v_a_3057_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3053_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3053_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg___boxed(lean_object* v_a_3067_, lean_object* v_b_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_3067_, v_b_3068_, v___y_3069_);
lean_dec_ref(v___y_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(size_t v_sz_3072_, size_t v_i_3073_, lean_object* v_bs_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = lean_usize_dec_lt(v_i_3073_, v_sz_3072_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_bs_3074_);
return v___x_3078_;
}
else
{
lean_object* v_v_3079_; lean_object* v___x_3080_; lean_object* v_bs_x27_3081_; lean_object* v___x_3082_; 
v_v_3079_ = lean_array_uget(v_bs_3074_, v_i_3073_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v_bs_x27_3081_ = lean_array_uset(v_bs_3074_, v_i_3073_, v___x_3080_);
v___x_3082_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_v_3079_, v___y_3075_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3084_ = ((size_t)1ULL);
v___x_3085_ = lean_usize_add(v_i_3073_, v___x_3084_);
v___x_3086_ = lean_array_uset(v_bs_x27_3081_, v_i_3073_, v_a_3083_);
v_i_3073_ = v___x_3085_;
v_bs_3074_ = v___x_3086_;
goto _start;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v_bs_x27_3081_);
v_a_3088_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3082_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3082_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg___boxed(lean_object* v_sz_3096_, lean_object* v_i_3097_, lean_object* v_bs_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
size_t v_sz_boxed_3101_; size_t v_i_boxed_3102_; lean_object* v_res_3103_; 
v_sz_boxed_3101_ = lean_unbox_usize(v_sz_3096_);
lean_dec(v_sz_3096_);
v_i_boxed_3102_ = lean_unbox_usize(v_i_3097_);
lean_dec(v_i_3097_);
v_res_3103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_boxed_3101_, v_i_boxed_3102_, v_bs_3098_, v___y_3099_);
lean_dec_ref(v___y_3099_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object* v_header_3104_, lean_object* v_indVal_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_argNames_3113_; lean_object* v_targetNames_3114_; lean_object* v_numParams_3115_; lean_object* v___x_3116_; lean_object* v_discrs_3117_; lean_object* v_lower_3119_; lean_object* v_upper_3120_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v_argNames_3113_ = lean_ctor_get(v_header_3104_, 1);
lean_inc_ref(v_argNames_3113_);
v_targetNames_3114_ = lean_ctor_get(v_header_3104_, 2);
lean_inc_ref(v_targetNames_3114_);
lean_dec_ref(v_header_3104_);
v_numParams_3115_ = lean_ctor_get(v_indVal_3105_, 1);
lean_inc(v_numParams_3115_);
lean_dec_ref(v_indVal_3105_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v_discrs_3117_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_3136_ = lean_array_get_size(v_argNames_3113_);
v___x_3137_ = lean_nat_dec_le(v_numParams_3115_, v___x_3116_);
if (v___x_3137_ == 0)
{
v_lower_3119_ = v_numParams_3115_;
v_upper_3120_ = v___x_3136_;
goto v___jp_3118_;
}
else
{
lean_dec(v_numParams_3115_);
v_lower_3119_ = v___x_3116_;
v_upper_3120_ = v___x_3136_;
goto v___jp_3118_;
}
v___jp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = l_Array_toSubarray___redArg(v_argNames_3113_, v_lower_3119_, v_upper_3120_);
v___x_3122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v___x_3121_, v_discrs_3117_, v_a_3110_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; size_t v_sz_3124_; size_t v___x_3125_; lean_object* v___x_3126_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v_sz_3124_ = lean_array_size(v_targetNames_3114_);
v___x_3125_ = ((size_t)0ULL);
v___x_3126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_3124_, v___x_3125_, v_targetNames_3114_, v_a_3110_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3135_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3131_ = l_Array_append___redArg(v_a_3123_, v_a_3127_);
lean_dec(v_a_3127_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3131_);
v___x_3133_ = v___x_3129_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_dec(v_a_3123_);
return v___x_3126_;
}
}
else
{
lean_dec_ref(v_targetNames_3114_);
return v___x_3122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs___boxed(lean_object* v_header_3138_, lean_object* v_indVal_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_3138_, v_indVal_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(lean_object* v_inst_3148_, lean_object* v_R_3149_, lean_object* v_a_3150_, lean_object* v_b_3151_, lean_object* v_c_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_3150_, v_b_3151_, v___y_3157_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(lean_object* v_inst_3161_, lean_object* v_R_3162_, lean_object* v_a_3163_, lean_object* v_b_3164_, lean_object* v_c_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(v_inst_3161_, v_R_3162_, v_a_3163_, v_b_3164_, v_c_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(size_t v_sz_3174_, size_t v_i_3175_, lean_object* v_bs_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_3174_, v_i_3175_, v_bs_3176_, v___y_3181_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(lean_object* v_sz_3185_, lean_object* v_i_3186_, lean_object* v_bs_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
size_t v_sz_boxed_3195_; size_t v_i_boxed_3196_; lean_object* v_res_3197_; 
v_sz_boxed_3195_ = lean_unbox_usize(v_sz_3185_);
lean_dec(v_sz_3185_);
v_i_boxed_3196_ = lean_unbox_usize(v_i_3186_);
lean_dec(v_i_3186_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_boxed_3195_, v_i_boxed_3196_, v_bs_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3197_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclNameGen(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Elab_Deriving_implicitBinderF = _init_l_Lean_Elab_Deriving_implicitBinderF();
lean_mark_persistent(l_Lean_Elab_Deriving_implicitBinderF);
l_Lean_Elab_Deriving_instBinderF = _init_l_Lean_Elab_Deriving_instBinderF();
lean_mark_persistent(l_Lean_Elab_Deriving_instBinderF);
l_Lean_Elab_Deriving_explicitBinderF = _init_l_Lean_Elab_Deriving_explicitBinderF();
lean_mark_persistent(l_Lean_Elab_Deriving_explicitBinderF);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeclNameGen(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclNameGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Util(builtin);
}
#ifdef __cplusplus
}
#endif
