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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Parser_Term_instBinder;
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "localinst"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(49, 72, 186, 87, 62, 92, 205, 11)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_270_ = l_Array_mkArray0(lean_box(0));
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
lean_object* v_snd_505_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v_a_514_; uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v_a_497_, v_upperBound_493_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_a_497_);
lean_dec(v_className_495_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_b_498_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_519_ = lean_array_fget_borrowed(v_xs_494_, v_a_497_);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_mk_empty_array_with_capacity(v___x_520_);
lean_inc(v___x_519_);
v___x_522_ = lean_array_push(v___x_521_, v___x_519_);
lean_inc(v_className_495_);
v___x_523_ = l_Lean_Meta_mkAppM(v_className_495_, v___x_522_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_Meta_isTypeCorrect(v_a_524_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint8_t v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_unbox(v_a_526_);
lean_dec(v_a_526_);
if (v___x_527_ == 0)
{
v_snd_505_ = v_b_498_;
goto v___jp_504_;
}
else
{
lean_object* v_ref_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_ref_528_ = lean_ctor_get(v___y_501_, 2);
v___x_529_ = lean_box(0);
v___x_530_ = lean_array_get_borrowed(v___x_529_, v_argNames_496_, v_a_497_);
v___x_531_ = 0;
v___x_532_ = l_Lean_SourceInfo_fromRef(v_ref_528_, v___x_531_);
v___x_533_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1));
v___x_534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2));
lean_inc_n(v___x_532_, 5);
v___x_535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_532_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_537_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_538_, 0, v___x_532_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_495_);
v___x_540_ = l_Lean_mkCIdent(v_className_495_);
lean_inc(v___x_530_);
v___x_541_ = l_Lean_mkIdent(v___x_530_);
v___x_542_ = l_Lean_Syntax_node1(v___x_532_, v___x_536_, v___x_541_);
v___x_543_ = l_Lean_Syntax_node2(v___x_532_, v___x_539_, v___x_540_, v___x_542_);
v___x_544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3));
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_532_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_Syntax_node4(v___x_532_, v___x_533_, v___x_535_, v___x_538_, v___x_543_, v___x_545_);
v___x_547_ = lean_array_push(v_b_498_, v___x_546_);
v_snd_505_ = v___x_547_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_525_, 1);
v_a_514_ = v_a_548_;
goto v___jp_513_;
}
}
else
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_523_, 1);
v_a_514_ = v_a_549_;
goto v___jp_513_;
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
if (v___y_511_ == 0)
{
lean_dec_ref(v___y_510_);
v_snd_505_ = v_b_498_;
goto v___jp_504_;
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_b_498_);
lean_dec(v_a_497_);
lean_dec(v_className_495_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___y_510_);
return v___x_512_;
}
}
v___jp_513_:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_Exception_isInterrupt(v_a_514_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
lean_inc_ref(v_a_514_);
v___x_516_ = l_Lean_Exception_isRuntime(v_a_514_);
v___y_510_ = v_a_514_;
v___y_511_ = v___x_516_;
goto v___jp_509_;
}
else
{
v___y_510_ = v_a_514_;
v___y_511_ = v___x_515_;
goto v___jp_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___boxed(lean_object* v_upperBound_550_, lean_object* v_xs_551_, lean_object* v_className_552_, lean_object* v_argNames_553_, lean_object* v_a_554_, lean_object* v_b_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_550_, v_xs_551_, v_className_552_, v_argNames_553_, v_a_554_, v_b_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v_argNames_553_);
lean_dec_ref(v_xs_551_);
lean_dec(v_upperBound_550_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(lean_object* v_className_564_, lean_object* v_argNames_565_, lean_object* v_xs_566_, lean_object* v_x_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_binders_577_; lean_object* v___x_578_; 
v___x_575_ = lean_array_get_size(v_xs_566_);
v___x_576_ = lean_unsigned_to_nat(0u);
v_binders_577_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v___x_575_, v_xs_566_, v_className_564_, v_argNames_565_, v___x_576_, v_binders_577_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed(lean_object* v_className_579_, lean_object* v_argNames_580_, lean_object* v_xs_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(v_className_579_, v_argNames_580_, v_xs_581_, v_x_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_xs_581_);
lean_dec_ref(v_argNames_580_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object* v_className_591_, lean_object* v_indVal_592_, lean_object* v_argNames_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_toConstantVal_601_; lean_object* v_numParams_602_; lean_object* v_type_603_; lean_object* v___f_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; 
v_toConstantVal_601_ = lean_ctor_get(v_indVal_592_, 0);
lean_inc_ref(v_toConstantVal_601_);
v_numParams_602_ = lean_ctor_get(v_indVal_592_, 1);
lean_inc(v_numParams_602_);
lean_dec_ref(v_indVal_592_);
v_type_603_ = lean_ctor_get(v_toConstantVal_601_, 2);
lean_inc_ref(v_type_603_);
lean_dec_ref(v_toConstantVal_601_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed), 11, 2);
lean_closure_set(v___f_604_, 0, v_className_591_);
lean_closure_set(v___f_604_, 1, v_argNames_593_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v_numParams_602_);
v___x_606_ = 0;
v___x_607_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_603_, v___x_605_, v___f_604_, v___x_606_, v___x_606_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___boxed(lean_object* v_className_608_, lean_object* v_indVal_609_, lean_object* v_argNames_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_608_, v_indVal_609_, v_argNames_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(lean_object* v_upperBound_619_, lean_object* v_xs_620_, lean_object* v_className_621_, lean_object* v_argNames_622_, lean_object* v_inst_623_, lean_object* v_R_624_, lean_object* v_a_625_, lean_object* v_b_626_, lean_object* v_c_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_619_, v_xs_620_, v_className_621_, v_argNames_622_, v_a_625_, v_b_626_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___boxed(lean_object* v_upperBound_636_, lean_object* v_xs_637_, lean_object* v_className_638_, lean_object* v_argNames_639_, lean_object* v_inst_640_, lean_object* v_R_641_, lean_object* v_a_642_, lean_object* v_b_643_, lean_object* v_c_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(v_upperBound_636_, v_xs_637_, v_className_638_, v_argNames_639_, v_inst_640_, v_R_641_, v_a_642_, v_b_643_, v_c_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v_argNames_639_);
lean_dec_ref(v_xs_637_);
lean_dec(v_upperBound_636_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(uint8_t v___x_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
if (lean_obj_tag(v_a_676_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = l_List_reverse___redArg(v_a_677_);
return v___x_678_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_710_; 
v_head_679_ = lean_ctor_get(v_a_676_, 0);
v_tail_680_ = lean_ctor_get(v_a_676_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_710_ == 0)
{
v___x_682_ = v_a_676_;
v_isShared_683_ = v_isSharedCheck_710_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_head_679_);
lean_dec(v_a_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_710_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___y_685_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1));
lean_inc(v_head_679_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_head_679_, v___x_692_);
if (v___x_693_ == 0)
{
v___y_685_ = v___x_693_;
goto v___jp_684_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Lean_Syntax_getArg(v_head_679_, v___x_694_);
v___x_696_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3));
lean_inc(v___x_695_);
v___x_697_ = l_Lean_Syntax_isOfKind(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec(v___x_695_);
v___y_685_ = v___x_697_;
goto v___jp_684_;
}
else
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = l_Lean_Syntax_getArg(v___x_695_, v___x_694_);
lean_dec(v___x_695_);
v___x_699_ = l_Lean_Syntax_matchesNull(v___x_698_, v___x_694_);
if (v___x_699_ == 0)
{
v___y_685_ = v___x_699_;
goto v___jp_684_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = l_Lean_Syntax_getArg(v_head_679_, v___x_700_);
v___x_702_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6));
lean_inc(v___x_701_);
v___x_703_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
lean_dec(v___x_701_);
v___y_685_ = v___x_703_;
goto v___jp_684_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = l_Lean_Syntax_getArg(v___x_701_, v___x_694_);
v___x_705_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8));
v___x_706_ = l_Lean_Syntax_matchesIdent(v___x_704_, v___x_705_);
lean_dec(v___x_704_);
if (v___x_706_ == 0)
{
lean_dec(v___x_701_);
v___y_685_ = v___x_706_;
goto v___jp_684_;
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = l_Lean_Syntax_getArg(v___x_701_, v___x_700_);
lean_dec(v___x_701_);
v___x_708_ = l_Lean_Syntax_matchesNull(v___x_707_, v___x_694_);
if (v___x_708_ == 0)
{
v___y_685_ = v___x_708_;
goto v___jp_684_;
}
else
{
lean_del_object(v___x_682_);
lean_dec(v_head_679_);
v_a_676_ = v_tail_680_;
goto _start;
}
}
}
}
}
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
if (v___x_675_ == 0)
{
lean_del_object(v___x_682_);
lean_dec(v_head_679_);
v_a_676_ = v_tail_680_;
goto _start;
}
else
{
lean_object* v___x_688_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_a_677_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_head_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_a_677_);
v___x_688_ = v_reuseFailAlloc_690_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_a_676_ = v_tail_680_;
v_a_677_ = v___x_688_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_682_);
lean_dec(v_head_679_);
v_a_676_ = v_tail_680_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___boxed(lean_object* v___x_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
uint8_t v___x_3707__boxed_714_; lean_object* v_res_715_; 
v___x_3707__boxed_714_ = lean_unbox(v___x_711_);
v_res_715_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_3707__boxed_714_, v_a_712_, v_a_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(uint8_t v___x_716_, lean_object* v_sc_717_){
_start:
{
lean_object* v_header_718_; lean_object* v_opts_719_; lean_object* v_currNamespace_720_; lean_object* v_openDecls_721_; lean_object* v_levelNames_722_; lean_object* v_varDecls_723_; lean_object* v_varUIds_724_; lean_object* v_includedVars_725_; lean_object* v_omittedVars_726_; uint8_t v_isNoncomputable_727_; uint8_t v_isPublic_728_; uint8_t v_isMeta_729_; lean_object* v_attrs_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_739_; 
v_header_718_ = lean_ctor_get(v_sc_717_, 0);
v_opts_719_ = lean_ctor_get(v_sc_717_, 1);
v_currNamespace_720_ = lean_ctor_get(v_sc_717_, 2);
v_openDecls_721_ = lean_ctor_get(v_sc_717_, 3);
v_levelNames_722_ = lean_ctor_get(v_sc_717_, 4);
v_varDecls_723_ = lean_ctor_get(v_sc_717_, 5);
v_varUIds_724_ = lean_ctor_get(v_sc_717_, 6);
v_includedVars_725_ = lean_ctor_get(v_sc_717_, 7);
v_omittedVars_726_ = lean_ctor_get(v_sc_717_, 8);
v_isNoncomputable_727_ = lean_ctor_get_uint8(v_sc_717_, sizeof(void*)*10);
v_isPublic_728_ = lean_ctor_get_uint8(v_sc_717_, sizeof(void*)*10 + 1);
v_isMeta_729_ = lean_ctor_get_uint8(v_sc_717_, sizeof(void*)*10 + 2);
v_attrs_730_ = lean_ctor_get(v_sc_717_, 9);
v_isSharedCheck_739_ = !lean_is_exclusive(v_sc_717_);
if (v_isSharedCheck_739_ == 0)
{
v___x_732_ = v_sc_717_;
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_attrs_730_);
lean_inc(v_omittedVars_726_);
lean_inc(v_includedVars_725_);
lean_inc(v_varUIds_724_);
lean_inc(v_varDecls_723_);
lean_inc(v_levelNames_722_);
lean_inc(v_openDecls_721_);
lean_inc(v_currNamespace_720_);
lean_inc(v_opts_719_);
lean_inc(v_header_718_);
lean_dec(v_sc_717_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = lean_box(0);
v___x_735_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_716_, v_attrs_730_, v___x_734_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 9, v___x_735_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_header_718_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_opts_719_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_currNamespace_720_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_openDecls_721_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_levelNames_722_);
lean_ctor_set(v_reuseFailAlloc_738_, 5, v_varDecls_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 6, v_varUIds_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 7, v_includedVars_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 8, v_omittedVars_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 9, v___x_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*10, v_isNoncomputable_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*10 + 1, v_isPublic_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*10 + 2, v_isMeta_729_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed(lean_object* v___x_740_, lean_object* v_sc_741_){
_start:
{
uint8_t v___x_3804__boxed_742_; lean_object* v_res_743_; 
v___x_3804__boxed_742_ = lean_unbox(v___x_740_);
v_res_743_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(v___x_3804__boxed_742_, v_sc_741_);
return v_res_743_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_box(1);
v___x_745_ = l_Lean_MessageData_ofFormat(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2));
v___x_750_ = l_Lean_MessageData_ofFormat(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
return v_x_751_;
}
else
{
lean_object* v_head_753_; lean_object* v_tail_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_776_; 
v_head_753_ = lean_ctor_get(v_x_752_, 0);
v_tail_754_ = lean_ctor_get(v_x_752_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_776_ == 0)
{
v___x_756_ = v_x_752_;
v_isShared_757_ = v_isSharedCheck_776_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_tail_754_);
lean_inc(v_head_753_);
lean_dec(v_x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_776_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_before_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_774_; 
v_before_758_ = lean_ctor_get(v_head_753_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_head_753_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_head_753_, 1);
lean_dec(v_unused_775_);
v___x_760_ = v_head_753_;
v_isShared_761_ = v_isSharedCheck_774_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_before_758_);
lean_dec(v_head_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_774_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 7);
lean_ctor_set(v___x_760_, 1, v___x_762_);
lean_ctor_set(v___x_760_, 0, v_x_751_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_x_751_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_773_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 7);
lean_ctor_set(v___x_756_, 1, v___x_765_);
lean_ctor_set(v___x_756_, 0, v___x_764_);
v___x_767_ = v___x_756_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_772_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = l_Lean_MessageData_ofSyntax(v_before_758_);
v___x_769_ = l_Lean_indentD(v___x_768_);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v_x_751_ = v___x_770_;
v_x_752_ = v_tail_754_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(lean_object* v_opts_777_, lean_object* v_opt_778_){
_start:
{
lean_object* v_name_779_; lean_object* v_defValue_780_; lean_object* v_map_781_; lean_object* v___x_782_; 
v_name_779_ = lean_ctor_get(v_opt_778_, 0);
v_defValue_780_ = lean_ctor_get(v_opt_778_, 1);
v_map_781_ = lean_ctor_get(v_opts_777_, 0);
v___x_782_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_781_, v_name_779_);
if (lean_obj_tag(v___x_782_) == 0)
{
uint8_t v___x_783_; 
v___x_783_ = lean_unbox(v_defValue_780_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; 
v_val_784_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_782_, 1);
if (lean_obj_tag(v_val_784_) == 1)
{
uint8_t v_v_785_; 
v_v_785_ = lean_ctor_get_uint8(v_val_784_, 0);
lean_dec_ref_known(v_val_784_, 0);
return v_v_785_;
}
else
{
uint8_t v___x_786_; 
lean_dec(v_val_784_);
v___x_786_ = lean_unbox(v_defValue_780_);
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_787_, lean_object* v_opt_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_787_, v_opt_788_);
lean_dec_ref(v_opt_788_);
lean_dec_ref(v_opts_787_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1));
v___x_795_ = l_Lean_MessageData_ofFormat(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(lean_object* v_msgData_796_, lean_object* v_macroStack_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_scopes_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_opts_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_800_ = lean_st_ref_get(v___y_798_);
v_scopes_801_ = lean_ctor_get(v___x_800_, 2);
lean_inc(v_scopes_801_);
lean_dec(v___x_800_);
v___x_802_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_803_ = l_List_head_x21___redArg(v___x_802_, v_scopes_801_);
lean_dec(v_scopes_801_);
v_opts_804_ = lean_ctor_get(v___x_803_, 1);
lean_inc_ref(v_opts_804_);
lean_dec(v___x_803_);
v___x_805_ = l_Lean_Elab_pp_macroStack;
v___x_806_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_804_, v___x_805_);
lean_dec_ref(v_opts_804_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v_macroStack_797_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v_msgData_796_);
return v___x_807_;
}
else
{
if (lean_obj_tag(v_macroStack_797_) == 0)
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_msgData_796_);
return v___x_808_;
}
else
{
lean_object* v_head_809_; lean_object* v_after_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_825_; 
v_head_809_ = lean_ctor_get(v_macroStack_797_, 0);
lean_inc(v_head_809_);
v_after_810_ = lean_ctor_get(v_head_809_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v_head_809_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_head_809_, 0);
lean_dec(v_unused_826_);
v___x_812_ = v_head_809_;
v_isShared_813_ = v_isSharedCheck_825_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_after_810_);
lean_dec(v_head_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_825_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 7);
lean_ctor_set(v___x_812_, 1, v___x_814_);
lean_ctor_set(v___x_812_, 0, v_msgData_796_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_msgData_796_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_824_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_msgData_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_817_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_MessageData_ofSyntax(v_after_810_);
v___x_820_ = l_Lean_indentD(v___x_819_);
v_msgData_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_821_, 0, v___x_818_);
lean_ctor_set(v_msgData_821_, 1, v___x_820_);
v___x_822_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_821_, v_macroStack_797_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_827_, lean_object* v_macroStack_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_827_, v_macroStack_828_, v___y_829_);
lean_dec(v___y_829_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_832_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
lean_ctor_set(v___x_837_, 3, v___x_836_);
lean_ctor_set(v___x_837_, 4, v___x_835_);
lean_ctor_set(v___x_837_, 5, v___x_835_);
lean_ctor_set(v___x_837_, 6, v___x_835_);
lean_ctor_set(v___x_837_, 7, v___x_835_);
lean_ctor_set(v___x_837_, 8, v___x_835_);
lean_ctor_set(v___x_837_, 9, v___x_835_);
lean_ctor_set(v___x_837_, 10, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(32u);
v___x_839_ = lean_mk_empty_array_with_capacity(v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_841_ = ((size_t)5ULL);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_unsigned_to_nat(32u);
v___x_844_ = lean_mk_empty_array_with_capacity(v___x_843_);
v___x_845_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3);
v___x_846_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
lean_ctor_set(v___x_846_, 2, v___x_842_);
lean_ctor_set(v___x_846_, 3, v___x_842_);
lean_ctor_set_usize(v___x_846_, 4, v___x_841_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_box(1);
v___x_848_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4);
v___x_849_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
v___x_850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_848_);
lean_ctor_set(v___x_850_, 2, v___x_847_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(lean_object* v_msgData_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_env_855_; lean_object* v___x_856_; lean_object* v_scopes_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_opts_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_854_ = lean_st_ref_get(v___y_852_);
v_env_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_854_);
v___x_856_ = lean_st_ref_get(v___y_852_);
v_scopes_857_ = lean_ctor_get(v___x_856_, 2);
lean_inc(v_scopes_857_);
lean_dec(v___x_856_);
v___x_858_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_859_ = l_List_head_x21___redArg(v___x_858_, v_scopes_857_);
lean_dec(v_scopes_857_);
v_opts_860_ = lean_ctor_get(v___x_859_, 1);
lean_inc_ref(v_opts_860_);
lean_dec(v___x_859_);
v___x_861_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2);
v___x_862_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5);
v___x_863_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_863_, 0, v_env_855_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
lean_ctor_set(v___x_863_, 3, v_opts_860_);
v___x_864_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v_msgData_851_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_866_, v___y_867_);
lean_dec(v___y_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Elab_Command_getRef___redArg(v___y_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_macroStack_876_; lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v_macroStack_876_ = lean_ctor_get(v___y_871_, 4);
v___x_877_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msg_870_, v___y_872_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = l_Lean_Elab_getBetterRef(v_a_875_, v_macroStack_876_);
lean_dec(v_a_875_);
lean_inc(v_macroStack_876_);
v___x_880_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_a_878_, v_macroStack_876_, v___y_872_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_879_);
lean_ctor_set(v___x_885_, 1, v_a_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 1);
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_msg_870_);
v_a_890_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_874_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_874_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg___boxed(lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_902_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(lean_object* v_constName_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v_env_914_; lean_object* v___x_915_; 
v___x_913_ = lean_st_ref_get(v___y_911_);
v_env_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_914_);
lean_dec(v___x_913_);
lean_inc(v_constName_909_);
v___x_915_ = l_Lean_isInductiveCore_x3f(v_env_914_, v_constName_909_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_916_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_917_ = 0;
v___x_918_ = l_Lean_MessageData_ofConstName(v_constName_909_, v___x_917_);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_921_, v___y_910_, v___y_911_);
return v___x_922_;
}
else
{
lean_object* v_val_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_constName_909_);
v_val_923_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_915_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_val_923_);
lean_dec(v___x_915_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 0);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_val_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___boxed(lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_constName_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(lean_object* v_as_x27_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
if (lean_obj_tag(v_as_x27_936_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_b_937_);
return v___x_941_;
}
else
{
lean_object* v_head_942_; lean_object* v_tail_943_; lean_object* v___x_944_; 
v_head_942_ = lean_ctor_get(v_as_x27_936_, 0);
v_tail_943_ = lean_ctor_get(v_as_x27_936_, 1);
lean_inc(v_head_942_);
v___x_944_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_head_942_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = lean_array_push(v_b_937_, v_a_945_);
v_as_x27_936_ = v_tail_943_;
v_b_937_ = v___x_946_;
goto _start;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_b_937_);
v_a_948_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_944_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_944_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg___boxed(lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_956_, v_b_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v_as_x27_956_);
return v_res_961_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(lean_object* v___y_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
uint8_t v___x_964_; 
v___x_964_ = 0;
return v___x_964_;
}
else
{
lean_object* v_head_965_; lean_object* v_tail_966_; uint8_t v___y_968_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_head_965_ = lean_ctor_get(v_x_963_, 0);
lean_inc_n(v_head_965_, 2);
v_tail_966_ = lean_ctor_get(v_x_963_, 1);
lean_inc(v_tail_966_);
lean_dec_ref_known(v_x_963_, 2);
v___x_970_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1));
v___x_971_ = l_Lean_Syntax_isOfKind(v_head_965_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_head_965_);
v___y_968_ = v___x_971_;
goto v___jp_967_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = l_Lean_Syntax_getArg(v_head_965_, v___x_972_);
v___x_974_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3));
lean_inc(v___x_973_);
v___x_975_ = l_Lean_Syntax_isOfKind(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_dec(v___x_973_);
lean_dec(v_head_965_);
v___y_968_ = v___x_975_;
goto v___jp_967_;
}
else
{
lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_976_ = l_Lean_Syntax_getArg(v___x_973_, v___x_972_);
lean_dec(v___x_973_);
v___x_977_ = l_Lean_Syntax_matchesNull(v___x_976_, v___x_972_);
if (v___x_977_ == 0)
{
lean_dec(v_head_965_);
v___y_968_ = v___x_977_;
goto v___jp_967_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = l_Lean_Syntax_getArg(v_head_965_, v___x_978_);
lean_dec(v_head_965_);
v___x_980_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6));
lean_inc(v___x_979_);
v___x_981_ = l_Lean_Syntax_isOfKind(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_dec(v___x_979_);
v___y_968_ = v___x_981_;
goto v___jp_967_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = l_Lean_Syntax_getArg(v___x_979_, v___x_972_);
v___x_983_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8));
v___x_984_ = l_Lean_Syntax_matchesIdent(v___x_982_, v___x_983_);
lean_dec(v___x_982_);
if (v___x_984_ == 0)
{
lean_dec(v___x_979_);
v___y_968_ = v___x_984_;
goto v___jp_967_;
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = l_Lean_Syntax_getArg(v___x_979_, v___x_978_);
lean_dec(v___x_979_);
v___x_986_ = l_Lean_Syntax_matchesNull(v___x_985_, v___x_972_);
if (v___x_986_ == 0)
{
v___y_968_ = v___x_986_;
goto v___jp_967_;
}
else
{
uint8_t v___x_987_; 
v___x_987_ = lean_nat_dec_lt(v___x_972_, v___y_962_);
v___y_968_ = v___x_987_;
goto v___jp_967_;
}
}
}
}
}
}
v___jp_967_:
{
if (v___y_968_ == 0)
{
v_x_963_ = v_tail_966_;
goto _start;
}
else
{
lean_dec(v_tail_966_);
return v___y_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5___boxed(lean_object* v___y_988_, lean_object* v_x_989_){
_start:
{
uint8_t v_res_990_; lean_object* v_r_991_; 
v_res_990_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___y_988_, v_x_989_);
lean_dec(v___y_988_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
else
{
lean_object* v_head_994_; lean_object* v_tail_995_; uint8_t v___x_996_; 
v_head_994_ = lean_ctor_get(v_x_992_, 0);
v_tail_995_ = lean_ctor_get(v_x_992_, 1);
v___x_996_ = l_Lean_isPrivateName(v_head_994_);
if (v___x_996_ == 0)
{
v_x_992_ = v_tail_995_;
goto _start;
}
else
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0___boxed(lean_object* v_x_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_x_998_);
lean_dec(v_x_998_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_eq(v_i_1002_, v_stop_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v_ctors_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_array_uget_borrowed(v_as_1001_, v_i_1002_);
v_ctors_1006_ = lean_ctor_get(v___x_1005_, 4);
v___x_1007_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_ctors_1006_);
if (v___x_1007_ == 0)
{
size_t v___x_1008_; size_t v___x_1009_; 
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_1002_, v___x_1008_);
v_i_1002_ = v___x_1009_;
goto _start;
}
else
{
return v___x_1007_;
}
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = 0;
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3___boxed(lean_object* v_as_1012_, lean_object* v_i_1013_, lean_object* v_stop_1014_){
_start:
{
size_t v_i_boxed_1015_; size_t v_stop_boxed_1016_; uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_i_boxed_1015_ = lean_unbox_usize(v_i_1013_);
lean_dec(v_i_1013_);
v_stop_boxed_1016_ = lean_unbox_usize(v_stop_1014_);
lean_dec(v_stop_1014_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_as_1012_, v_i_boxed_1015_, v_stop_boxed_1016_);
lean_dec_ref(v_as_1012_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object* v_typeName_1027_, lean_object* v_cont_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; 
lean_inc(v_typeName_1027_);
v___x_1032_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_typeName_1027_, v_a_1029_, v_a_1030_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v_all_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v_all_1034_ = lean_ctor_get(v_a_1033_, 3);
lean_inc(v_all_1034_);
lean_dec(v_a_1033_);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1037_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_all_1034_, v___x_1036_, v_a_1029_, v_a_1030_);
lean_dec(v_all_1034_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = lean_array_get_size(v_a_1038_);
v___x_1040_ = lean_nat_dec_lt(v___x_1035_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec(v_a_1038_);
lean_dec(v_typeName_1027_);
lean_inc(v_a_1030_);
lean_inc_ref(v_a_1029_);
v___x_1041_ = lean_apply_3(v_cont_1028_, v_a_1029_, v_a_1030_, lean_box(0));
return v___x_1041_;
}
else
{
if (v___x_1040_ == 0)
{
lean_object* v___x_1042_; 
lean_dec(v_a_1038_);
lean_dec(v_typeName_1027_);
lean_inc(v_a_1030_);
lean_inc_ref(v_a_1029_);
v___x_1042_ = lean_apply_3(v_cont_1028_, v_a_1029_, v_a_1030_, lean_box(0));
return v___x_1042_;
}
else
{
size_t v___x_1043_; size_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = lean_usize_of_nat(v___x_1039_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_a_1038_, v___x_1043_, v___x_1044_);
lean_dec(v_a_1038_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec(v_typeName_1027_);
lean_inc(v_a_1030_);
lean_inc_ref(v_a_1029_);
v___x_1046_ = lean_apply_3(v_cont_1028_, v_a_1029_, v_a_1030_, lean_box(0));
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v___f_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_box(v___x_1045_);
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1048_, 0, v___x_1047_);
v___x_1049_ = l_Lean_isPrivateName(v_typeName_1027_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Elab_Command_getScope___redArg(v_a_1030_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v_attrs_1052_; uint8_t v___x_1053_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v_attrs_1052_ = lean_ctor_get(v_a_1051_, 9);
lean_inc(v_attrs_1052_);
lean_dec(v_a_1051_);
v___x_1053_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___x_1039_, v_attrs_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec(v_typeName_1027_);
v___x_1054_ = l_Lean_Elab_Command_withScope___redArg(v___f_1048_, v_cont_1028_, v_a_1029_, v_a_1030_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___f_1048_);
lean_dec_ref(v_cont_1028_);
v___x_1055_ = lean_obj_once(&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2, &l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once, _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2);
v___x_1056_ = l_Lean_MessageData_ofConstName(v_typeName_1027_, v___x_1049_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4, &l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once, _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_1059_, v_a_1029_, v_a_1030_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___f_1048_);
lean_dec_ref(v_cont_1028_);
lean_dec(v_typeName_1027_);
v_a_1069_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1050_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1050_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_typeName_1027_);
v___x_1077_ = l_Lean_Elab_Command_withScope___redArg(v___f_1048_, v_cont_1028_, v_a_1029_, v_a_1030_);
return v___x_1077_;
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_cont_1028_);
lean_dec(v_typeName_1027_);
v_a_1078_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1037_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1037_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_cont_1028_);
lean_dec(v_typeName_1027_);
v_a_1086_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1032_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1032_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___boxed(lean_object* v_typeName_1094_, lean_object* v_cont_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1094_, v_cont_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors(lean_object* v_00_u03b1_1100_, lean_object* v_typeName_1101_, lean_object* v_cont_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1101_, v_cont_1102_, v_a_1103_, v_a_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_typeName_1108_, lean_object* v_cont_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Elab_Deriving_withoutExposeFromCtors(v_00_u03b1_1107_, v_typeName_1108_, v_cont_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(lean_object* v_as_1114_, lean_object* v_as_x27_1115_, lean_object* v_b_1116_, lean_object* v_a_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_1115_, v_b_1116_, v___y_1118_, v___y_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___boxed(lean_object* v_as_1122_, lean_object* v_as_x27_1123_, lean_object* v_b_1124_, lean_object* v_a_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(v_as_1122_, v_as_x27_1123_, v_b_1124_, v_a_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_as_x27_1123_);
lean_dec(v_as_1122_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(lean_object* v_msgData_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_1130_, v___y_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___boxed(lean_object* v_msgData_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(v_msgData_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(lean_object* v_00_u03b1_1140_, lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_1141_, v___y_1142_, v___y_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(v_00_u03b1_1146_, v_msg_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(lean_object* v_msgData_1152_, lean_object* v_macroStack_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_1152_, v_macroStack_1153_, v___y_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___boxed(lean_object* v_msgData_1158_, lean_object* v_macroStack_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(v_msgData_1158_, v_macroStack_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(size_t v_sz_1164_, size_t v_i_1165_, lean_object* v_bs_1166_){
_start:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_lt(v_i_1165_, v_sz_1164_);
if (v___x_1167_ == 0)
{
return v_bs_1166_;
}
else
{
lean_object* v_v_1168_; lean_object* v___x_1169_; lean_object* v_bs_x27_1170_; size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
v_v_1168_ = lean_array_uget(v_bs_1166_, v_i_1165_);
v___x_1169_ = lean_unsigned_to_nat(0u);
v_bs_x27_1170_ = lean_array_uset(v_bs_1166_, v_i_1165_, v___x_1169_);
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_add(v_i_1165_, v___x_1171_);
v___x_1173_ = lean_array_uset(v_bs_x27_1170_, v_i_1165_, v_v_1168_);
v_i_1165_ = v___x_1172_;
v_bs_1166_ = v___x_1173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1___boxed(lean_object* v_sz_1175_, lean_object* v_i_1176_, lean_object* v_bs_1177_){
_start:
{
size_t v_sz_boxed_1178_; size_t v_i_boxed_1179_; lean_object* v_res_1180_; 
v_sz_boxed_1178_ = lean_unbox_usize(v_sz_1175_);
lean_dec(v_sz_1175_);
v_i_boxed_1179_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_res_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_boxed_1178_, v_i_boxed_1179_, v_bs_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(lean_object* v_msgData_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_env_1188_; lean_object* v___x_1189_; lean_object* v_toCold_1190_; lean_object* v_mctx_1191_; lean_object* v_lctx_1192_; lean_object* v_options_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1187_ = lean_st_ref_get(v___y_1185_);
v_env_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_env_1188_);
lean_dec(v___x_1187_);
v___x_1189_ = lean_st_ref_get(v___y_1183_);
v_toCold_1190_ = lean_ctor_get(v___y_1184_, 0);
v_mctx_1191_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_mctx_1191_);
lean_dec(v___x_1189_);
v_lctx_1192_ = lean_ctor_get(v___y_1182_, 2);
v_options_1193_ = lean_ctor_get(v_toCold_1190_, 2);
lean_inc_ref(v_options_1193_);
lean_inc_ref(v_lctx_1192_);
v___x_1194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1194_, 0, v_env_1188_);
lean_ctor_set(v___x_1194_, 1, v_mctx_1191_);
lean_ctor_set(v___x_1194_, 2, v_lctx_1192_);
lean_ctor_set(v___x_1194_, 3, v_options_1193_);
v___x_1195_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_msgData_1181_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1204_, lean_object* v_macroStack_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_toCold_1208_; lean_object* v_options_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_toCold_1208_ = lean_ctor_get(v___y_1206_, 0);
v_options_1209_ = lean_ctor_get(v_toCold_1208_, 2);
v___x_1210_ = l_Lean_Elab_pp_macroStack;
v___x_1211_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_options_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
lean_dec(v_macroStack_1205_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_msgData_1204_);
return v___x_1212_;
}
else
{
if (lean_obj_tag(v_macroStack_1205_) == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_msgData_1204_);
return v___x_1213_;
}
else
{
lean_object* v_head_1214_; lean_object* v_after_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1230_; 
v_head_1214_ = lean_ctor_get(v_macroStack_1205_, 0);
lean_inc(v_head_1214_);
v_after_1215_ = lean_ctor_get(v_head_1214_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_head_1214_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_head_1214_, 0);
lean_dec(v_unused_1231_);
v___x_1217_ = v_head_1214_;
v_isShared_1218_ = v_isSharedCheck_1230_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_after_1215_);
lean_dec(v_head_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1230_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 7);
lean_ctor_set(v___x_1217_, 1, v___x_1219_);
lean_ctor_set(v___x_1217_, 0, v_msgData_1204_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_msgData_1204_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_msgData_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1222_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_MessageData_ofSyntax(v_after_1215_);
v___x_1225_ = l_Lean_indentD(v___x_1224_);
v_msgData_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1226_, 0, v___x_1223_);
lean_ctor_set(v_msgData_1226_, 1, v___x_1225_);
v___x_1227_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_1226_, v_macroStack_1205_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1232_, lean_object* v_macroStack_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1232_, v_macroStack_1233_, v___y_1234_);
lean_dec_ref(v___y_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_ref_1245_; lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v_macroStack_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1259_; 
v_ref_1245_ = lean_ctor_get(v___y_1242_, 2);
v___x_1246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1237_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v_macroStack_1248_ = lean_ctor_get(v___y_1238_, 1);
v___x_1249_ = l_Lean_Elab_getBetterRef(v_ref_1245_, v_macroStack_1248_);
lean_inc(v_macroStack_1248_);
v___x_1250_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_a_1247_, v_macroStack_1248_, v___y_1242_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1249_);
lean_ctor_set(v___x_1255_, 1, v_a_1251_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 1);
lean_ctor_set(v___x_1253_, 0, v___x_1255_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; lean_object* v_env_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_st_ref_get(v___y_1275_);
v_env_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_env_1278_);
lean_dec(v___x_1277_);
lean_inc(v_constName_1269_);
v___x_1279_ = l_Lean_isInductiveCore_x3f(v_env_1278_, v_constName_1269_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1280_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_1281_ = 0;
v___x_1282_ = l_Lean_MessageData_ofConstName(v_constName_1269_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1280_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v___x_1285_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1286_;
}
else
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_constName_1269_);
v_val_1287_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1279_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v___x_1279_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_val_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0___boxed(lean_object* v_constName_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_constName_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object* v_className_1305_, lean_object* v_indName_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_indName_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_n(v_a_1315_, 2);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_1315_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_n(v_a_1317_, 2);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_1317_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v_ref_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_1315_, v_a_1317_, v_a_1311_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1320_);
v_ref_1322_ = lean_ctor_get(v_a_1311_, 2);
v___x_1323_ = 0;
v___x_1324_ = l_Lean_SourceInfo_fromRef(v_ref_1322_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
v___x_1326_ = l_Lean_mkCIdent(v_className_1305_);
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1324_);
v___x_1328_ = l_Lean_Syntax_node1(v___x_1324_, v___x_1327_, v_a_1321_);
v___x_1329_ = l_Lean_Syntax_node2(v___x_1324_, v___x_1325_, v___x_1326_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstName___closed__0));
v_sz_1331_ = lean_array_size(v_a_1319_);
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_1331_, v___x_1332_, v_a_1319_);
v___x_1334_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_1330_, v___x_1333_, v___x_1329_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1334_;
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_a_1317_);
lean_dec(v_a_1315_);
lean_dec(v_className_1305_);
v_a_1335_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1318_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1318_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_a_1315_);
lean_dec(v_className_1305_);
v_a_1343_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1316_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1316_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_className_1305_);
v_a_1351_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1314_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1314_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName___boxed(lean_object* v_className_1359_, lean_object* v_indName_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Elab_Deriving_mkInstName(v_className_1359_, v_indName_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(lean_object* v_00_u03b1_1369_, lean_object* v_msg_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_msg_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(v_00_u03b1_1379_, v_msg_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(lean_object* v_msgData_1389_, lean_object* v_macroStack_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1389_, v_macroStack_1390_, v___y_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1399_, lean_object* v_macroStack_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_1399_, v_macroStack_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(lean_object* v_as_x27_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
if (lean_obj_tag(v_as_x27_1409_) == 0)
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_b_1410_);
return v___x_1418_;
}
else
{
lean_object* v_head_1419_; lean_object* v_tail_1420_; lean_object* v___x_1421_; 
v_head_1419_ = lean_ctor_get(v_as_x27_1409_, 0);
v_tail_1420_ = lean_ctor_get(v_as_x27_1409_, 1);
lean_inc(v_head_1419_);
v___x_1421_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_head_1419_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = lean_array_push(v_b_1410_, v_a_1422_);
v_as_x27_1409_ = v_tail_1420_;
v_b_1410_ = v___x_1423_;
goto _start;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_b_1410_);
v_a_1425_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1421_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1421_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg___boxed(lean_object* v_as_x27_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1433_, v_b_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v_as_x27_1433_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
if (lean_obj_tag(v_a_1443_) == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = l_List_reverse___redArg(v_a_1444_);
return v___x_1445_;
}
else
{
lean_object* v_head_1446_; lean_object* v_tail_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1456_; 
v_head_1446_ = lean_ctor_get(v_a_1443_, 0);
v_tail_1447_ = lean_ctor_get(v_a_1443_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1443_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1449_ = v_a_1443_;
v_isShared_1450_ = v_isSharedCheck_1456_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_tail_1447_);
lean_inc(v_head_1446_);
lean_dec(v_a_1443_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1456_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = l_Lean_MessageData_ofName(v_head_1446_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v_a_1444_);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_a_1444_);
v___x_1453_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
v_a_1443_ = v_tail_1447_;
v_a_1444_ = v___x_1453_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1457_; double v___x_1458_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_float_of_nat(v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(lean_object* v_cls_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_ref_1469_; lean_object* v___x_1470_; lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1515_; 
v_ref_1469_ = lean_ctor_get(v___y_1466_, 2);
v___x_1470_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1515_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1515_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v_traceState_1476_; lean_object* v_env_1477_; lean_object* v_nextMacroScope_1478_; lean_object* v_ngen_1479_; lean_object* v_auxDeclNGen_1480_; lean_object* v_cache_1481_; lean_object* v_messages_1482_; lean_object* v_infoState_1483_; lean_object* v_snapshotTasks_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1514_; 
v___x_1475_ = lean_st_ref_take(v___y_1467_);
v_traceState_1476_ = lean_ctor_get(v___x_1475_, 4);
v_env_1477_ = lean_ctor_get(v___x_1475_, 0);
v_nextMacroScope_1478_ = lean_ctor_get(v___x_1475_, 1);
v_ngen_1479_ = lean_ctor_get(v___x_1475_, 2);
v_auxDeclNGen_1480_ = lean_ctor_get(v___x_1475_, 3);
v_cache_1481_ = lean_ctor_get(v___x_1475_, 5);
v_messages_1482_ = lean_ctor_get(v___x_1475_, 6);
v_infoState_1483_ = lean_ctor_get(v___x_1475_, 7);
v_snapshotTasks_1484_ = lean_ctor_get(v___x_1475_, 8);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1486_ = v___x_1475_;
v_isShared_1487_ = v_isSharedCheck_1514_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snapshotTasks_1484_);
lean_inc(v_infoState_1483_);
lean_inc(v_messages_1482_);
lean_inc(v_cache_1481_);
lean_inc(v_traceState_1476_);
lean_inc(v_auxDeclNGen_1480_);
lean_inc(v_ngen_1479_);
lean_inc(v_nextMacroScope_1478_);
lean_inc(v_env_1477_);
lean_dec(v___x_1475_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1514_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint64_t v_tid_1488_; lean_object* v_traces_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1513_; 
v_tid_1488_ = lean_ctor_get_uint64(v_traceState_1476_, sizeof(void*)*1);
v_traces_1489_ = lean_ctor_get(v_traceState_1476_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_traceState_1476_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1491_ = v_traceState_1476_;
v_isShared_1492_ = v_isSharedCheck_1513_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_traces_1489_);
lean_dec(v_traceState_1476_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1513_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; double v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0);
v___x_1495_ = 0;
v___x_1496_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1));
v___x_1497_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1497_, 0, v_cls_1462_);
lean_ctor_set(v___x_1497_, 1, v___x_1493_);
lean_ctor_set(v___x_1497_, 2, v___x_1496_);
lean_ctor_set_float(v___x_1497_, sizeof(void*)*3, v___x_1494_);
lean_ctor_set_float(v___x_1497_, sizeof(void*)*3 + 8, v___x_1494_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*3 + 16, v___x_1495_);
v___x_1498_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2));
v___x_1499_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v_a_1471_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
lean_inc(v_ref_1469_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_ref_1469_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = l_Lean_PersistentArray_push___redArg(v_traces_1489_, v___x_1500_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1501_);
v___x_1503_ = v___x_1491_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1501_);
lean_ctor_set_uint64(v_reuseFailAlloc_1512_, sizeof(void*)*1, v_tid_1488_);
v___x_1503_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1503_);
v___x_1505_ = v___x_1486_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_env_1477_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_nextMacroScope_1478_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_ngen_1479_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_auxDeclNGen_1480_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1511_, 5, v_cache_1481_);
lean_ctor_set(v_reuseFailAlloc_1511_, 6, v_messages_1482_);
lean_ctor_set(v_reuseFailAlloc_1511_, 7, v_infoState_1483_);
lean_ctor_set(v_reuseFailAlloc_1511_, 8, v_snapshotTasks_1484_);
v___x_1505_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = lean_st_ref_put(v___y_1467_, v___x_1505_);
v___x_1507_ = lean_box(0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1507_);
v___x_1509_ = v___x_1473_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___boxed(lean_object* v_cls_1516_, lean_object* v_msg_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1516_, v_msg_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(lean_object* v_fnPrefix_1525_, lean_object* v_a_1526_, lean_object* v_range_1527_, lean_object* v_b_1528_, lean_object* v_i_1529_){
_start:
{
lean_object* v_stop_1531_; lean_object* v_step_1532_; uint8_t v___x_1533_; 
v_stop_1531_ = lean_ctor_get(v_range_1527_, 1);
v_step_1532_ = lean_ctor_get(v_range_1527_, 2);
v___x_1533_ = lean_nat_dec_lt(v_i_1529_, v_stop_1531_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec(v_i_1529_);
lean_dec(v_a_1526_);
lean_dec_ref(v_fnPrefix_1525_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_b_1528_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0));
lean_inc_ref(v_fnPrefix_1525_);
v___x_1537_ = lean_string_append(v_fnPrefix_1525_, v___x_1536_);
v___x_1538_ = lean_nat_add(v_i_1529_, v___x_1535_);
v___x_1539_ = l_Nat_reprFast(v___x_1538_);
v___x_1540_ = lean_string_append(v___x_1537_, v___x_1539_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = lean_box(0);
v___x_1542_ = l_Lean_Name_str___override(v___x_1541_, v___x_1540_);
lean_inc(v_a_1526_);
v___x_1543_ = l_Lean_Name_append(v_a_1526_, v___x_1542_);
v___x_1544_ = lean_array_push(v_b_1528_, v___x_1543_);
v___x_1545_ = lean_nat_add(v_i_1529_, v_step_1532_);
lean_dec(v_i_1529_);
v_b_1528_ = v___x_1544_;
v_i_1529_ = v___x_1545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___boxed(lean_object* v_fnPrefix_1547_, lean_object* v_a_1548_, lean_object* v_range_1549_, lean_object* v_b_1550_, lean_object* v_i_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1547_, v_a_1548_, v_range_1549_, v_b_1550_, v_i_1551_);
lean_dec_ref(v_range_1549_);
return v_res_1553_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__5(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__4));
v___x_1564_ = l_Lean_Name_append(v___x_1563_, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__7(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__6));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__9(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__8));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext(lean_object* v_className_1571_, lean_object* v_fnPrefix_1572_, lean_object* v_typeName_1573_, uint8_t v_supportsRec_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; 
lean_inc(v_typeName_1573_);
v___x_1582_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_typeName_1573_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v_all_1584_; uint8_t v_isRec_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_all_1584_ = lean_ctor_get(v_a_1583_, 3);
v_isRec_1585_ = lean_ctor_get_uint8(v_a_1583_, sizeof(void*)*6);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1588_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_all_1584_, v___x_1587_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1590_ = l_Lean_Elab_Deriving_mkInstName(v_className_1571_, v_typeName_1573_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1655_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1655_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1655_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___y_1596_; uint8_t v___y_1597_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1606_; lean_object* v_auxFunNames_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = l_List_lengthTR___redArg(v_all_1584_);
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = lean_nat_dec_eq(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_a_1650_; 
v___x_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1586_);
lean_ctor_set(v___x_1648_, 1, v___x_1645_);
lean_ctor_set(v___x_1648_, 2, v___x_1646_);
lean_inc(v_a_1591_);
v___x_1649_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1572_, v_a_1591_, v___x_1648_, v___x_1587_, v___x_1586_);
lean_dec_ref_known(v___x_1648_, 3);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v_auxFunNames_1612_ = v_a_1650_;
v___y_1613_ = v_a_1575_;
v___y_1614_ = v_a_1576_;
v___y_1615_ = v_a_1577_;
v___y_1616_ = v_a_1578_;
v___y_1617_ = v_a_1579_;
v___y_1618_ = v_a_1580_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v___x_1645_);
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Lean_Name_str___override(v___x_1651_, v_fnPrefix_1572_);
lean_inc(v_a_1591_);
v___x_1653_ = l_Lean_Name_append(v_a_1591_, v___x_1652_);
v___x_1654_ = lean_array_push(v___x_1587_, v___x_1653_);
v_auxFunNames_1612_ = v___x_1654_;
v___y_1613_ = v_a_1575_;
v___y_1614_ = v_a_1576_;
v___y_1615_ = v_a_1577_;
v___y_1616_ = v_a_1578_;
v___y_1617_ = v_a_1579_;
v___y_1618_ = v_a_1580_;
goto v___jp_1611_;
}
v___jp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1598_, 0, v_a_1591_);
lean_ctor_set(v___x_1598_, 1, v_a_1589_);
lean_ctor_set(v___x_1598_, 2, v___y_1596_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*3, v___y_1597_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1598_);
v___x_1600_ = v___x_1593_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
v___jp_1602_:
{
if (v___y_1604_ == 0)
{
if (v_isRec_1585_ == 0)
{
v___y_1596_ = v___y_1603_;
v___y_1597_ = v_isRec_1585_;
goto v___jp_1595_;
}
else
{
if (v_supportsRec_1574_ == 0)
{
v___y_1596_ = v___y_1603_;
v___y_1597_ = v_isRec_1585_;
goto v___jp_1595_;
}
else
{
v___y_1596_ = v___y_1603_;
v___y_1597_ = v___y_1604_;
goto v___jp_1595_;
}
}
}
else
{
v___y_1596_ = v___y_1603_;
v___y_1597_ = v___y_1604_;
goto v___jp_1595_;
}
}
v___jp_1605_:
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_InductiveVal_isNested(v_a_1583_);
lean_dec(v_a_1583_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_array_get_size(v_a_1589_);
v___x_1610_ = lean_nat_dec_lt(v___x_1608_, v___x_1609_);
v___y_1603_ = v___y_1606_;
v___y_1604_ = v___x_1610_;
goto v___jp_1602_;
}
else
{
v___y_1603_ = v___y_1606_;
v___y_1604_ = v___x_1607_;
goto v___jp_1602_;
}
}
v___jp_1611_:
{
lean_object* v_toCold_1619_; lean_object* v_options_1620_; uint8_t v_hasTrace_1621_; 
v_toCold_1619_ = lean_ctor_get(v___y_1617_, 0);
v_options_1620_ = lean_ctor_get(v_toCold_1619_, 2);
v_hasTrace_1621_ = lean_ctor_get_uint8(v_options_1620_, sizeof(void*)*1);
if (v_hasTrace_1621_ == 0)
{
v___y_1606_ = v_auxFunNames_1612_;
goto v___jp_1605_;
}
else
{
lean_object* v_inheritedTraceOptions_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_inheritedTraceOptions_1622_ = lean_ctor_get(v_toCold_1619_, 11);
v___x_1623_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1624_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__5, &l_Lean_Elab_Deriving_mkContext___closed__5_once, _init_l_Lean_Elab_Deriving_mkContext___closed__5);
v___x_1625_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1622_, v_options_1620_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1606_ = v_auxFunNames_1612_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1626_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__7, &l_Lean_Elab_Deriving_mkContext___closed__7_once, _init_l_Lean_Elab_Deriving_mkContext___closed__7);
lean_inc(v_a_1591_);
v___x_1627_ = l_Lean_MessageData_ofName(v_a_1591_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__9, &l_Lean_Elab_Deriving_mkContext___closed__9_once, _init_l_Lean_Elab_Deriving_mkContext___closed__9);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
lean_inc_ref(v_auxFunNames_1612_);
v___x_1631_ = lean_array_to_list(v_auxFunNames_1612_);
v___x_1632_ = lean_box(0);
v___x_1633_ = l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(v___x_1631_, v___x_1632_);
v___x_1634_ = l_Lean_MessageData_ofList(v___x_1633_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1630_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v___x_1623_, v___x_1635_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_dec_ref_known(v___x_1636_, 1);
v___y_1606_ = v_auxFunNames_1612_;
goto v___jp_1605_;
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_auxFunNames_1612_);
lean_del_object(v___x_1593_);
lean_dec(v_a_1591_);
lean_dec(v_a_1589_);
lean_dec(v_a_1583_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
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
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_a_1589_);
lean_dec(v_a_1583_);
lean_dec_ref(v_fnPrefix_1572_);
v_a_1656_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1590_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1590_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_a_1583_);
lean_dec(v_typeName_1573_);
lean_dec_ref(v_fnPrefix_1572_);
lean_dec(v_className_1571_);
v_a_1664_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1588_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1588_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_typeName_1573_);
lean_dec_ref(v_fnPrefix_1572_);
lean_dec(v_className_1571_);
v_a_1672_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1582_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1582_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object* v_className_1680_, lean_object* v_fnPrefix_1681_, lean_object* v_typeName_1682_, lean_object* v_supportsRec_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
uint8_t v_supportsRec_boxed_1691_; lean_object* v_res_1692_; 
v_supportsRec_boxed_1691_ = lean_unbox(v_supportsRec_1683_);
v_res_1692_ = l_Lean_Elab_Deriving_mkContext(v_className_1680_, v_fnPrefix_1681_, v_typeName_1682_, v_supportsRec_boxed_1691_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(lean_object* v_as_1693_, lean_object* v_as_x27_1694_, lean_object* v_b_1695_, lean_object* v_a_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1694_, v_b_1695_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___boxed(lean_object* v_as_1705_, lean_object* v_as_x27_1706_, lean_object* v_b_1707_, lean_object* v_a_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(v_as_1705_, v_as_x27_1706_, v_b_1707_, v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v_as_x27_1706_);
lean_dec(v_as_1705_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(lean_object* v_cls_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1717_, v_msg_1718_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___boxed(lean_object* v_cls_1727_, lean_object* v_msg_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(v_cls_1727_, v_msg_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(lean_object* v_fnPrefix_1737_, lean_object* v_a_1738_, lean_object* v_range_1739_, lean_object* v_b_1740_, lean_object* v_i_1741_, lean_object* v_hs_1742_, lean_object* v_hl_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1737_, v_a_1738_, v_range_1739_, v_b_1740_, v_i_1741_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(lean_object* v_fnPrefix_1752_, lean_object* v_a_1753_, lean_object* v_range_1754_, lean_object* v_b_1755_, lean_object* v_i_1756_, lean_object* v_hs_1757_, lean_object* v_hl_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_1752_, v_a_1753_, v_range_1754_, v_b_1755_, v_i_1756_, v_hs_1757_, v_hl_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v_range_1754_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v_array_1769_; lean_object* v_start_1770_; lean_object* v_stop_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1784_; 
v_array_1769_ = lean_ctor_get(v_a_1767_, 0);
v_start_1770_ = lean_ctor_get(v_a_1767_, 1);
v_stop_1771_ = lean_ctor_get(v_a_1767_, 2);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1773_ = v_a_1767_;
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_stop_1771_);
lean_inc(v_start_1770_);
lean_inc(v_array_1769_);
lean_dec(v_a_1767_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_lt(v_start_1770_, v_stop_1771_);
if (v___x_1775_ == 0)
{
lean_del_object(v___x_1773_);
lean_dec(v_stop_1771_);
lean_dec(v_start_1770_);
lean_dec_ref(v_array_1769_);
return v_b_1768_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_start_1770_, v___x_1776_);
lean_inc_ref(v_array_1769_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1777_);
v___x_1779_ = v___x_1773_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_array_1769_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_stop_1771_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_array_fget(v_array_1769_, v_start_1770_);
lean_dec(v_start_1770_);
lean_dec_ref(v_array_1769_);
v___x_1781_ = lean_array_push(v_b_1768_, v___x_1780_);
v_a_1767_ = v___x_1779_;
v_b_1768_ = v___x_1781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_ref_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_ref_1792_ = lean_ctor_get(v___y_1789_, 2);
v___x_1793_ = 0;
v___x_1794_ = l_Lean_SourceInfo_fromRef(v_ref_1792_, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(lean_object* v_upperBound_1841_, lean_object* v___x_1842_, lean_object* v_ctx_1843_, lean_object* v_argNames_1844_, lean_object* v_className_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_nat_dec_lt(v_a_1846_, v_upperBound_1841_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_b_1847_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_array_fget_borrowed(v___x_1842_, v_a_1846_);
lean_inc(v___x_1857_);
v___x_1858_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_1857_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_auxFunNames_1860_; lean_object* v_numParams_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_lower_1865_; lean_object* v_upper_1866_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v_auxFunNames_1860_ = lean_ctor_get(v_ctx_1843_, 2);
v_numParams_1861_ = lean_ctor_get(v___x_1857_, 1);
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_array_get_borrowed(v___x_1862_, v_auxFunNames_1860_, v_a_1846_);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_array_get_size(v_a_1859_);
v___x_1960_ = lean_nat_dec_le(v_numParams_1861_, v___x_1958_);
if (v___x_1960_ == 0)
{
lean_inc(v_numParams_1861_);
v_lower_1865_ = v_numParams_1861_;
v_upper_1866_ = v___x_1959_;
goto v___jp_1864_;
}
else
{
v_lower_1865_ = v___x_1958_;
v_upper_1866_ = v___x_1959_;
goto v___jp_1864_;
}
v___jp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = l_Array_toSubarray___redArg(v_a_1859_, v_lower_1865_, v_upper_1866_);
lean_inc_ref(v___x_1867_);
v___x_1868_ = l_Subarray_copy___redArg(v___x_1867_);
v___x_1869_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_1868_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_a_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1861_);
lean_inc_ref(v_argNames_1844_);
v___x_1872_ = l_Array_toSubarray___redArg(v_argNames_1844_, v___x_1871_, v_numParams_1861_);
v___x_1873_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_1874_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1872_, v___x_1873_);
v___x_1875_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1867_, v___x_1873_);
v_a_1876_ = l_Array_append___redArg(v___x_1874_, v___x_1875_);
lean_dec_ref(v___x_1875_);
v___x_1877_ = lean_array_get_size(v_a_1876_);
v___x_1878_ = l_Array_toSubarray___redArg(v_a_1876_, v___x_1871_, v___x_1877_);
v___x_1879_ = l_Subarray_copy___redArg(v___x_1878_);
lean_inc(v___x_1857_);
v___x_1880_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_1857_, v___x_1879_, v___y_1852_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_ref_1882_; lean_object* v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_ref_1882_ = lean_ctor_get(v___y_1852_, 2);
v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_n(v_a_1884_, 2);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = 0;
v___x_1886_ = l_Lean_SourceInfo_fromRef(v_ref_1882_, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1886_);
v___x_1888_ = l_Lean_Syntax_node1(v___x_1886_, v___x_1887_, v_a_1881_);
v___x_1889_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0));
v___x_1890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_a_1884_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_1892_ = l_Lean_Core_mkFreshUserName(v___x_1891_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_n(v_a_1895_, 8);
lean_dec_ref_known(v___x_1894_, 1);
lean_inc(v___x_1863_);
v___x_1896_ = l_Lean_mkIdent(v___x_1863_);
lean_inc_n(v_a_1884_, 2);
v___x_1897_ = l_Lean_Syntax_node1(v_a_1884_, v___x_1887_, v___x_1896_);
v___x_1898_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_1899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1884_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_1845_);
v___x_1901_ = l_Lean_mkCIdent(v_className_1845_);
v___x_1902_ = l_Lean_Syntax_node2(v___x_1886_, v___x_1900_, v___x_1901_, v___x_1888_);
v___x_1903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5));
v___x_1904_ = l_Lean_Syntax_node3(v_a_1884_, v___x_1903_, v___x_1890_, v___x_1897_, v___x_1899_);
v___x_1905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7));
v___x_1906_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9));
v___x_1907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11));
v___x_1908_ = l_Lean_mkIdent(v_a_1893_);
v___x_1909_ = l_Lean_Syntax_node1(v_a_1895_, v___x_1907_, v___x_1908_);
v___x_1910_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_1911_ = l_Array_append___redArg(v___x_1910_, v_a_1870_);
lean_dec(v_a_1870_);
v___x_1912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1895_);
lean_ctor_set(v___x_1912_, 1, v___x_1887_);
lean_ctor_set(v___x_1912_, 2, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13));
v___x_1914_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_1915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_a_1895_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_Syntax_node2(v_a_1895_, v___x_1913_, v___x_1915_, v___x_1902_);
v___x_1917_ = l_Lean_Syntax_node1(v_a_1895_, v___x_1887_, v___x_1916_);
v___x_1918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_1919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1895_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_Syntax_node5(v_a_1895_, v___x_1906_, v___x_1909_, v___x_1912_, v___x_1917_, v___x_1919_, v___x_1904_);
v___x_1921_ = l_Lean_Syntax_node1(v_a_1895_, v___x_1905_, v___x_1920_);
v___x_1922_ = lean_array_push(v_b_1847_, v___x_1921_);
v___x_1923_ = lean_unsigned_to_nat(1u);
v___x_1924_ = lean_nat_add(v_a_1846_, v___x_1923_);
lean_dec(v_a_1846_);
v_a_1846_ = v___x_1924_;
v_b_1847_ = v___x_1922_;
goto _start;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_a_1893_);
lean_dec_ref_known(v___x_1890_, 2);
lean_dec(v___x_1888_);
lean_dec(v___x_1886_);
lean_dec(v_a_1884_);
lean_dec(v_a_1870_);
lean_dec_ref(v_b_1847_);
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
v_a_1926_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1894_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1894_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref_known(v___x_1890_, 2);
lean_dec(v___x_1888_);
lean_dec(v___x_1886_);
lean_dec(v_a_1884_);
lean_dec(v_a_1870_);
lean_dec_ref(v_b_1847_);
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
v_a_1934_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1892_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1892_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1881_);
lean_dec(v_a_1870_);
lean_dec_ref(v_b_1847_);
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
v_a_1942_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1883_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1883_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_a_1870_);
lean_dec_ref(v_b_1847_);
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
v_a_1950_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1880_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1880_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_b_1847_);
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_b_1847_);
lean_dec(v_a_1846_);
lean_dec(v_className_1845_);
lean_dec_ref(v_argNames_1844_);
v_a_1961_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1858_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1858_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___boxed(lean_object* v_upperBound_1969_, lean_object* v___x_1970_, lean_object* v_ctx_1971_, lean_object* v_argNames_1972_, lean_object* v_className_1973_, lean_object* v_a_1974_, lean_object* v_b_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_1969_, v___x_1970_, v_ctx_1971_, v_argNames_1972_, v_className_1973_, v_a_1974_, v_b_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec_ref(v_ctx_1971_);
lean_dec_ref(v___x_1970_);
lean_dec(v_upperBound_1969_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object* v_ctx_1984_, lean_object* v_className_1985_, lean_object* v_argNames_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_typeInfos_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_letDecls_1997_; lean_object* v___x_1998_; 
v_typeInfos_1994_ = lean_ctor_get(v_ctx_1984_, 1);
v___x_1995_ = lean_array_get_size(v_typeInfos_1994_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v_letDecls_1997_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_1998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v___x_1995_, v_typeInfos_1994_, v_ctx_1984_, v_argNames_1986_, v_className_1985_, v___x_1996_, v_letDecls_1997_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_1999_, lean_object* v_className_2000_, lean_object* v_argNames_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_1999_, v_className_2000_, v_argNames_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec_ref(v_ctx_1999_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2010_, lean_object* v_R_2011_, lean_object* v_a_2012_, lean_object* v_b_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2012_, v_b_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(lean_object* v_upperBound_2015_, lean_object* v___x_2016_, lean_object* v_ctx_2017_, lean_object* v_argNames_2018_, lean_object* v_className_2019_, lean_object* v_inst_2020_, lean_object* v_R_2021_, lean_object* v_a_2022_, lean_object* v_b_2023_, lean_object* v_c_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_2015_, v___x_2016_, v_ctx_2017_, v_argNames_2018_, v_className_2019_, v_a_2022_, v_b_2023_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2033_ = _args[0];
lean_object* v___x_2034_ = _args[1];
lean_object* v_ctx_2035_ = _args[2];
lean_object* v_argNames_2036_ = _args[3];
lean_object* v_className_2037_ = _args[4];
lean_object* v_inst_2038_ = _args[5];
lean_object* v_R_2039_ = _args[6];
lean_object* v_a_2040_ = _args[7];
lean_object* v_b_2041_ = _args[8];
lean_object* v_c_2042_ = _args[9];
lean_object* v___y_2043_ = _args[10];
lean_object* v___y_2044_ = _args[11];
lean_object* v___y_2045_ = _args[12];
lean_object* v___y_2046_ = _args[13];
lean_object* v___y_2047_ = _args[14];
lean_object* v___y_2048_ = _args[15];
lean_object* v___y_2049_ = _args[16];
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(v_upperBound_2033_, v___x_2034_, v_ctx_2035_, v_argNames_2036_, v_className_2037_, v_inst_2038_, v_R_2039_, v_a_2040_, v_b_2041_, v_c_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v_ctx_2035_);
lean_dec_ref(v___x_2034_);
lean_dec(v_upperBound_2033_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(lean_object* v_as_2064_, size_t v_i_2065_, size_t v_stop_2066_, lean_object* v_b_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_eq(v_i_2065_, v_stop_2066_);
if (v___x_2070_ == 0)
{
lean_object* v_ref_2071_; size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_ref_2071_ = lean_ctor_get(v___y_2068_, 2);
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_sub(v_i_2065_, v___x_2072_);
v___x_2074_ = lean_array_uget_borrowed(v_as_2064_, v___x_2073_);
v___x_2075_ = l_Lean_SourceInfo_fromRef(v_ref_2071_, v___x_2070_);
v___x_2076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0));
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1));
lean_inc_n(v___x_2075_, 4);
v___x_2078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2076_);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3));
v___x_2080_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2075_);
lean_ctor_set(v___x_2082_, 1, v___x_2080_);
lean_ctor_set(v___x_2082_, 2, v___x_2081_);
v___x_2083_ = l_Lean_Syntax_node1(v___x_2075_, v___x_2079_, v___x_2082_);
v___x_2084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4));
v___x_2085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2075_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
lean_inc(v___x_2074_);
v___x_2086_ = l_Lean_Syntax_node5(v___x_2075_, v___x_2077_, v___x_2078_, v___x_2083_, v___x_2074_, v___x_2085_, v_b_2067_);
v_i_2065_ = v___x_2073_;
v_b_2067_ = v___x_2086_;
goto _start;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_b_2067_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(lean_object* v_as_2089_, lean_object* v_i_2090_, lean_object* v_stop_2091_, lean_object* v_b_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
size_t v_i_boxed_2095_; size_t v_stop_boxed_2096_; lean_object* v_res_2097_; 
v_i_boxed_2095_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_stop_boxed_2096_ = lean_unbox_usize(v_stop_2091_);
lean_dec(v_stop_2091_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2089_, v_i_boxed_2095_, v_stop_boxed_2096_, v_b_2092_, v___y_2093_);
lean_dec_ref(v___y_2093_);
lean_dec_ref(v_as_2089_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet(lean_object* v_letDecls_2098_, lean_object* v_body_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2107_ = lean_array_get_size(v_letDecls_2098_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_nat_dec_lt(v___x_2108_, v___x_2107_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_body_2099_);
return v___x_2110_;
}
else
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_usize_of_nat(v___x_2107_);
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_letDecls_2098_, v___x_2111_, v___x_2112_, v_body_2099_, v_a_2104_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet___boxed(lean_object* v_letDecls_2114_, lean_object* v_body_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Elab_Deriving_mkLet(v_letDecls_2114_, v_body_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_letDecls_2114_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2124_, v_i_2125_, v_stop_2126_, v_b_2127_, v___y_2132_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(lean_object* v_as_2136_, lean_object* v_i_2137_, lean_object* v_stop_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
size_t v_i_boxed_2147_; size_t v_stop_boxed_2148_; lean_object* v_res_2149_; 
v_i_boxed_2147_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_stop_boxed_2148_ = lean_unbox_usize(v_stop_2138_);
lean_dec(v_stop_2138_);
v_res_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_2136_, v_i_boxed_2147_, v_stop_boxed_2148_, v_b_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v_as_2136_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(lean_object* v___f_2159_, lean_object* v___x_2160_, lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_instName_2164_, lean_object* v___x_2165_, lean_object* v___x_2166_, lean_object* v_b_2167_, lean_object* v_____r_2168_, lean_object* v_val_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
lean_inc(v___y_2175_);
lean_inc_ref(v___y_2174_);
lean_inc(v___y_2173_);
lean_inc_ref(v___y_2172_);
lean_inc(v___y_2171_);
lean_inc_ref(v___y_2170_);
v___x_2177_ = lean_apply_7(v___f_2159_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, lean_box(0));
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2227_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2227_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2227_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2182_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0));
v___x_2183_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1));
lean_inc_ref_n(v___x_2161_, 8);
lean_inc_ref_n(v___x_2160_, 8);
v___x_2184_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2182_, v___x_2183_);
v___x_2185_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2));
v___x_2186_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2182_, v___x_2185_);
v___x_2187_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc_n(v___x_2162_, 2);
lean_inc_n(v_a_2178_, 14);
v___x_2188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2178_);
lean_ctor_set(v___x_2188_, 1, v___x_2162_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_inc_ref_n(v___x_2188_, 12);
v___x_2189_ = l_Lean_Syntax_node7(v_a_2178_, v___x_2186_, v___x_2188_, v___x_2188_, v___x_2188_, v___x_2188_, v___x_2188_, v___x_2188_, v___x_2188_);
v___x_2190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3));
v___x_2191_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2182_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2));
lean_inc_ref(v___x_2163_);
v___x_2193_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2163_, v___x_2192_);
v___x_2194_ = l_Lean_Syntax_node1(v_a_2178_, v___x_2193_, v___x_2188_);
v___x_2195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_a_2178_);
lean_ctor_set(v___x_2195_, 1, v___x_2190_);
v___x_2196_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4));
v___x_2197_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2182_, v___x_2196_);
v___x_2198_ = l_Lean_mkIdent(v_instName_2164_);
v___x_2199_ = l_Lean_Syntax_node2(v_a_2178_, v___x_2197_, v___x_2198_, v___x_2188_);
v___x_2200_ = l_Lean_Syntax_node1(v_a_2178_, v___x_2162_, v___x_2199_);
v___x_2201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5));
v___x_2202_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2182_, v___x_2201_);
v___x_2203_ = l_Array_append___redArg(v___x_2187_, v___x_2165_);
v___x_2204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2204_, 0, v_a_2178_);
lean_ctor_set(v___x_2204_, 1, v___x_2162_);
lean_ctor_set(v___x_2204_, 2, v___x_2203_);
v___x_2205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12));
v___x_2206_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2163_, v___x_2205_);
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2178_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = l_Lean_Syntax_node2(v_a_2178_, v___x_2206_, v___x_2208_, v___x_2166_);
v___x_2210_ = l_Lean_Syntax_node2(v_a_2178_, v___x_2202_, v___x_2204_, v___x_2209_);
v___x_2211_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6));
v___x_2212_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2182_, v___x_2211_);
v___x_2213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_2214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2178_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7));
v___x_2216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8));
v___x_2217_ = l_Lean_Name_mkStr4(v___x_2160_, v___x_2161_, v___x_2215_, v___x_2216_);
v___x_2218_ = l_Lean_Syntax_node2(v_a_2178_, v___x_2217_, v___x_2188_, v___x_2188_);
v___x_2219_ = l_Lean_Syntax_node4(v_a_2178_, v___x_2212_, v___x_2214_, v_val_2169_, v___x_2218_, v___x_2188_);
v___x_2220_ = l_Lean_Syntax_node6(v_a_2178_, v___x_2191_, v___x_2194_, v___x_2195_, v___x_2188_, v___x_2200_, v___x_2210_, v___x_2219_);
v___x_2221_ = l_Lean_Syntax_node2(v_a_2178_, v___x_2184_, v___x_2189_, v___x_2220_);
v___x_2222_ = lean_array_push(v_b_2167_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2223_);
v___x_2225_ = v___x_2180_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_val_2169_);
lean_dec_ref(v_b_2167_);
lean_dec(v___x_2166_);
lean_dec(v_instName_2164_);
lean_dec_ref(v___x_2163_);
lean_dec(v___x_2162_);
lean_dec_ref(v___x_2161_);
lean_dec_ref(v___x_2160_);
v_a_2228_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2177_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2177_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___f_2236_ = _args[0];
lean_object* v___x_2237_ = _args[1];
lean_object* v___x_2238_ = _args[2];
lean_object* v___x_2239_ = _args[3];
lean_object* v___x_2240_ = _args[4];
lean_object* v_instName_2241_ = _args[5];
lean_object* v___x_2242_ = _args[6];
lean_object* v___x_2243_ = _args[7];
lean_object* v_b_2244_ = _args[8];
lean_object* v_____r_2245_ = _args[9];
lean_object* v_val_2246_ = _args[10];
lean_object* v___y_2247_ = _args[11];
lean_object* v___y_2248_ = _args[12];
lean_object* v___y_2249_ = _args[13];
lean_object* v___y_2250_ = _args[14];
lean_object* v___y_2251_ = _args[15];
lean_object* v___y_2252_ = _args[16];
lean_object* v___y_2253_ = _args[17];
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2236_, v___x_2237_, v___x_2238_, v___x_2239_, v___x_2240_, v_instName_2241_, v___x_2242_, v___x_2243_, v_b_2244_, v_____r_2245_, v_val_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v___x_2242_);
return v_res_2254_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_2255_, lean_object* v_as_2256_, size_t v_i_2257_, size_t v_stop_2258_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_eq(v_i_2257_, v_stop_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_array_uget_borrowed(v_as_2256_, v_i_2257_);
v___x_2261_ = lean_name_eq(v_a_2255_, v___x_2260_);
if (v___x_2261_ == 0)
{
size_t v___x_2262_; size_t v___x_2263_; 
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_add(v_i_2257_, v___x_2262_);
v_i_2257_ = v___x_2263_;
goto _start;
}
else
{
return v___x_2261_;
}
}
else
{
uint8_t v___x_2265_; 
v___x_2265_ = 0;
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_2266_, lean_object* v_as_2267_, lean_object* v_i_2268_, lean_object* v_stop_2269_){
_start:
{
size_t v_i_boxed_2270_; size_t v_stop_boxed_2271_; uint8_t v_res_2272_; lean_object* v_r_2273_; 
v_i_boxed_2270_ = lean_unbox_usize(v_i_2268_);
lean_dec(v_i_2268_);
v_stop_boxed_2271_ = lean_unbox_usize(v_stop_2269_);
lean_dec(v_stop_2269_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2266_, v_as_2267_, v_i_boxed_2270_, v_stop_boxed_2271_);
lean_dec_ref(v_as_2267_);
lean_dec(v_a_2266_);
v_r_2273_ = lean_box(v_res_2272_);
return v_r_2273_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(lean_object* v_as_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_array_get_size(v_as_2274_);
v___x_2278_ = lean_nat_dec_lt(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
return v___x_2278_;
}
else
{
if (v___x_2278_ == 0)
{
return v___x_2278_;
}
else
{
size_t v___x_2279_; size_t v___x_2280_; uint8_t v___x_2281_; 
v___x_2279_ = ((size_t)0ULL);
v___x_2280_ = lean_usize_of_nat(v___x_2277_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2275_, v_as_2274_, v___x_2279_, v___x_2280_);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0___boxed(lean_object* v_as_2282_, lean_object* v_a_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_as_2282_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(lean_object* v_upperBound_2287_, lean_object* v___x_2288_, lean_object* v_typeNames_2289_, lean_object* v_className_2290_, lean_object* v_ctx_2291_, uint8_t v_useAnonCtor_2292_, lean_object* v_a_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_a_2303_; lean_object* v___y_2308_; uint8_t v___x_2327_; 
v___x_2327_ = lean_nat_dec_lt(v_a_2293_, v_upperBound_2287_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_b_2294_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v_toConstantVal_2331_; lean_object* v_name_2332_; uint8_t v___x_2333_; 
v___x_2329_ = l_Lean_instInhabitedInductiveVal_default;
v___x_2330_ = lean_array_get_borrowed(v___x_2329_, v___x_2288_, v_a_2293_);
v_toConstantVal_2331_ = lean_ctor_get(v___x_2330_, 0);
v_name_2332_ = lean_ctor_get(v_toConstantVal_2331_, 0);
v___x_2333_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_typeNames_2289_, v_name_2332_);
if (v___x_2333_ == 0)
{
v_a_2303_ = v_b_2294_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2334_; 
lean_inc(v___x_2330_);
v___x_2334_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_2330_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc_n(v_a_2335_, 2);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2335_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
lean_inc(v_a_2335_);
lean_inc(v___x_2330_);
lean_inc(v_className_2290_);
v___x_2338_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2290_, v___x_2330_, v_a_2335_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
lean_inc(v___x_2330_);
v___x_2340_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_2330_, v_a_2335_, v___y_2299_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_instName_2342_; lean_object* v_auxFunNames_2343_; lean_object* v_ref_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v_instName_2342_ = lean_ctor_get(v_ctx_2291_, 0);
v_auxFunNames_2343_ = lean_ctor_get(v_ctx_2291_, 2);
v_ref_2344_ = lean_ctor_get(v___y_2299_, 2);
v___f_2345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0));
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_array_get_borrowed(v___x_2346_, v_auxFunNames_2343_, v_a_2293_);
v___x_2348_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0));
v___x_2349_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1));
v___x_2350_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2));
v___x_2351_ = l_Array_append___redArg(v_a_2337_, v_a_2339_);
lean_dec(v_a_2339_);
v___x_2352_ = 0;
v___x_2353_ = l_Lean_SourceInfo_fromRef(v_ref_2344_, v___x_2352_);
v___x_2354_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_2290_);
v___x_2355_ = l_Lean_mkCIdent(v_className_2290_);
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_2353_);
v___x_2357_ = l_Lean_Syntax_node1(v___x_2353_, v___x_2356_, v_a_2341_);
v___x_2358_ = l_Lean_Syntax_node2(v___x_2353_, v___x_2354_, v___x_2355_, v___x_2357_);
lean_inc(v___x_2347_);
v___x_2359_ = l_Lean_mkIdent(v___x_2347_);
if (v_useAnonCtor_2292_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_box(0);
lean_inc(v_instName_2342_);
v___x_2361_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2345_, v___x_2348_, v___x_2349_, v___x_2356_, v___x_2350_, v_instName_2342_, v___x_2351_, v___x_2358_, v_b_2294_, v___x_2360_, v___x_2359_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec_ref(v___x_2351_);
v___y_2308_ = v___x_2361_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2362_; 
v___x_2362_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc_n(v_a_2363_, 4);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5));
v___x_2365_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__0));
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_a_2363_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_Syntax_node1(v_a_2363_, v___x_2356_, v___x_2359_);
v___x_2368_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_2369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_a_2363_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_Syntax_node3(v_a_2363_, v___x_2364_, v___x_2366_, v___x_2367_, v___x_2369_);
v___x_2371_ = lean_box(0);
lean_inc(v_instName_2342_);
v___x_2372_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2345_, v___x_2348_, v___x_2349_, v___x_2356_, v___x_2350_, v_instName_2342_, v___x_2351_, v___x_2358_, v_b_2294_, v___x_2371_, v___x_2370_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec_ref(v___x_2351_);
v___y_2308_ = v___x_2372_;
goto v___jp_2307_;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v___x_2359_);
lean_dec(v___x_2358_);
lean_dec_ref(v___x_2351_);
lean_dec_ref(v_b_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v_a_2373_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2362_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2362_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_a_2339_);
lean_dec(v_a_2337_);
lean_dec_ref(v_b_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v_a_2381_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2340_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2340_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_a_2337_);
lean_dec(v_a_2335_);
lean_dec_ref(v_b_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v_a_2389_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2338_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2338_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_dec(v_a_2335_);
lean_dec_ref(v_b_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
return v___x_2336_;
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_b_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v_a_2397_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2334_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2334_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
v___jp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = lean_nat_add(v_a_2293_, v___x_2304_);
lean_dec(v_a_2293_);
v_a_2293_ = v___x_2305_;
v_b_2294_ = v_a_2303_;
goto _start;
}
v___jp_2307_:
{
if (lean_obj_tag(v___y_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2318_; 
v_a_2309_ = lean_ctor_get(v___y_2308_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___y_2308_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2311_ = v___y_2308_;
v_isShared_2312_ = v_isSharedCheck_2318_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___y_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2318_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
if (lean_obj_tag(v_a_2309_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; 
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v_a_2313_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v_a_2309_, 1);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v_a_2313_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
else
{
lean_object* v_a_2317_; 
lean_del_object(v___x_2311_);
v_a_2317_ = lean_ctor_get(v_a_2309_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v_a_2309_, 1);
v_a_2303_ = v_a_2317_;
goto v___jp_2302_;
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_a_2293_);
lean_dec_ref(v_ctx_2291_);
lean_dec(v_className_2290_);
v_a_2319_ = lean_ctor_get(v___y_2308_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___y_2308_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___y_2308_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___y_2308_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_upperBound_2405_, lean_object* v___x_2406_, lean_object* v_typeNames_2407_, lean_object* v_className_2408_, lean_object* v_ctx_2409_, lean_object* v_useAnonCtor_2410_, lean_object* v_a_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_useAnonCtor_boxed_2420_; lean_object* v_res_2421_; 
v_useAnonCtor_boxed_2420_ = lean_unbox(v_useAnonCtor_2410_);
v_res_2421_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2405_, v___x_2406_, v_typeNames_2407_, v_className_2408_, v_ctx_2409_, v_useAnonCtor_boxed_2420_, v_a_2411_, v_b_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v_typeNames_2407_);
lean_dec_ref(v___x_2406_);
lean_dec(v_upperBound_2405_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object* v_ctx_2422_, lean_object* v_className_2423_, lean_object* v_typeNames_2424_, uint8_t v_useAnonCtor_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_typeInfos_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_instances_2436_; lean_object* v___x_2437_; 
v_typeInfos_2433_ = lean_ctor_get(v_ctx_2422_, 1);
lean_inc_ref(v_typeInfos_2433_);
v___x_2434_ = lean_array_get_size(v_typeInfos_2433_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_instances_2436_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v___x_2434_, v_typeInfos_2433_, v_typeNames_2424_, v_className_2423_, v_ctx_2422_, v_useAnonCtor_2425_, v___x_2435_, v_instances_2436_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec_ref(v_typeInfos_2433_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds___boxed(lean_object* v_ctx_2438_, lean_object* v_className_2439_, lean_object* v_typeNames_2440_, lean_object* v_useAnonCtor_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
uint8_t v_useAnonCtor_boxed_2449_; lean_object* v_res_2450_; 
v_useAnonCtor_boxed_2449_ = lean_unbox(v_useAnonCtor_2441_);
v_res_2450_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_2438_, v_className_2439_, v_typeNames_2440_, v_useAnonCtor_boxed_2449_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec_ref(v_typeNames_2440_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(lean_object* v_upperBound_2451_, lean_object* v___x_2452_, lean_object* v_typeNames_2453_, lean_object* v_className_2454_, lean_object* v_ctx_2455_, uint8_t v_useAnonCtor_2456_, lean_object* v_inst_2457_, lean_object* v_R_2458_, lean_object* v_a_2459_, lean_object* v_b_2460_, lean_object* v_c_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2451_, v___x_2452_, v_typeNames_2453_, v_className_2454_, v_ctx_2455_, v_useAnonCtor_2456_, v_a_2459_, v_b_2460_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2470_ = _args[0];
lean_object* v___x_2471_ = _args[1];
lean_object* v_typeNames_2472_ = _args[2];
lean_object* v_className_2473_ = _args[3];
lean_object* v_ctx_2474_ = _args[4];
lean_object* v_useAnonCtor_2475_ = _args[5];
lean_object* v_inst_2476_ = _args[6];
lean_object* v_R_2477_ = _args[7];
lean_object* v_a_2478_ = _args[8];
lean_object* v_b_2479_ = _args[9];
lean_object* v_c_2480_ = _args[10];
lean_object* v___y_2481_ = _args[11];
lean_object* v___y_2482_ = _args[12];
lean_object* v___y_2483_ = _args[13];
lean_object* v___y_2484_ = _args[14];
lean_object* v___y_2485_ = _args[15];
lean_object* v___y_2486_ = _args[16];
lean_object* v___y_2487_ = _args[17];
_start:
{
uint8_t v_useAnonCtor_boxed_2488_; lean_object* v_res_2489_; 
v_useAnonCtor_boxed_2488_ = lean_unbox(v_useAnonCtor_2475_);
v_res_2489_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(v_upperBound_2470_, v___x_2471_, v_typeNames_2472_, v_className_2473_, v_ctx_2474_, v_useAnonCtor_boxed_2488_, v_inst_2476_, v_R_2477_, v_a_2478_, v_b_2479_, v_c_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v_typeNames_2472_);
lean_dec_ref(v___x_2471_);
lean_dec(v_upperBound_2470_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg(lean_object* v_varName_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_ref_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_ref_2499_ = lean_ctor_get(v_a_2497_, 2);
v___x_2500_ = 0;
v___x_2501_ = l_Lean_SourceInfo_fromRef(v_ref_2499_, v___x_2500_);
v___x_2502_ = ((lean_object*)(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1));
v___x_2503_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2504_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc(v___x_2501_);
v___x_2505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2501_);
lean_ctor_set(v___x_2505_, 1, v___x_2503_);
lean_ctor_set(v___x_2505_, 2, v___x_2504_);
v___x_2506_ = l_Lean_mkIdent(v_varName_2496_);
v___x_2507_ = l_Lean_Syntax_node2(v___x_2501_, v___x_2502_, v___x_2505_, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(lean_object* v_varName_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2509_, v_a_2510_);
lean_dec_ref(v_a_2510_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr(lean_object* v_varName_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2513_, v_a_2518_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___boxed(lean_object* v_varName_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Elab_Deriving_mkDiscr(v_varName_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(lean_object* v_upperBound_2534_, lean_object* v_a_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_nat_dec_lt(v_a_2535_, v_upperBound_2534_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; 
lean_dec(v_a_2535_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_b_2536_);
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1));
v___x_2543_ = l_Lean_Core_mkFreshUserName(v___x_2542_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = lean_array_push(v_b_2536_, v_a_2544_);
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_a_2535_, v___x_2546_);
lean_dec(v_a_2535_);
v_a_2535_ = v___x_2547_;
v_b_2536_ = v___x_2545_;
goto _start;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_b_2536_);
lean_dec(v_a_2535_);
v_a_2549_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2543_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2543_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___boxed(lean_object* v_upperBound_2557_, lean_object* v_a_2558_, lean_object* v_b_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2557_, v_a_2558_, v_b_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v_upperBound_2557_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(lean_object* v_a_2572_, size_t v_sz_2573_, size_t v_i_2574_, lean_object* v_bs_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_usize_dec_lt(v_i_2574_, v_sz_2573_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
lean_dec(v_a_2572_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_bs_2575_);
return v___x_2579_;
}
else
{
lean_object* v_ref_2580_; lean_object* v_v_2581_; lean_object* v___x_2582_; lean_object* v_bs_x27_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v_ref_2580_ = lean_ctor_get(v___y_2576_, 2);
v_v_2581_ = lean_array_uget(v_bs_2575_, v_i_2574_);
v___x_2582_ = lean_unsigned_to_nat(0u);
v_bs_x27_2583_ = lean_array_uset(v_bs_2575_, v_i_2574_, v___x_2582_);
v___x_2584_ = 0;
v___x_2585_ = l_Lean_SourceInfo_fromRef(v_ref_2580_, v___x_2584_);
v___x_2586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1));
v___x_2587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2));
lean_inc_n(v___x_2585_, 6);
v___x_2588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2585_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2590_ = l_Lean_mkIdent(v_v_2581_);
v___x_2591_ = l_Lean_Syntax_node1(v___x_2585_, v___x_2589_, v___x_2590_);
v___x_2592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2585_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
lean_inc(v_a_2572_);
v___x_2594_ = l_Lean_Syntax_node2(v___x_2585_, v___x_2589_, v___x_2593_, v_a_2572_);
v___x_2595_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2585_);
lean_ctor_set(v___x_2596_, 1, v___x_2589_);
lean_ctor_set(v___x_2596_, 2, v___x_2595_);
v___x_2597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3));
v___x_2598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2585_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = l_Lean_Syntax_node5(v___x_2585_, v___x_2586_, v___x_2588_, v___x_2591_, v___x_2594_, v___x_2596_, v___x_2598_);
v___x_2600_ = ((size_t)1ULL);
v___x_2601_ = lean_usize_add(v_i_2574_, v___x_2600_);
v___x_2602_ = lean_array_uset(v_bs_x27_2583_, v_i_2574_, v___x_2599_);
v_i_2574_ = v___x_2601_;
v_bs_2575_ = v___x_2602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___boxed(lean_object* v_a_2604_, lean_object* v_sz_2605_, lean_object* v_i_2606_, lean_object* v_bs_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
size_t v_sz_boxed_2610_; size_t v_i_boxed_2611_; lean_object* v_res_2612_; 
v_sz_boxed_2610_ = lean_unbox_usize(v_sz_2605_);
lean_dec(v_sz_2605_);
v_i_boxed_2611_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2604_, v_sz_boxed_2610_, v_i_boxed_2611_, v_bs_2607_, v___y_2608_);
lean_dec_ref(v___y_2608_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object* v_className_2613_, lean_object* v_arity_2614_, lean_object* v_indVal_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; 
lean_inc_ref(v_indVal_2615_);
v___x_2623_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc_n(v_a_2624_, 2);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2624_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
lean_inc(v_a_2624_);
lean_inc_ref(v_indVal_2615_);
v___x_2627_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_2615_, v_a_2624_, v_a_2620_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_2631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_arity_2614_, v___x_2629_, v___x_2630_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
lean_inc(v_a_2624_);
v___x_2633_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2613_, v_indVal_2615_, v_a_2624_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; size_t v_sz_2635_; size_t v___x_2636_; lean_object* v___x_2637_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v_sz_2635_ = lean_array_size(v_a_2632_);
v___x_2636_ = ((size_t)0ULL);
lean_inc(v_a_2632_);
lean_inc(v_a_2628_);
v___x_2637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2628_, v_sz_2635_, v___x_2636_, v_a_2632_, v_a_2620_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2648_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2648_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2648_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2642_ = l_Array_append___redArg(v_a_2626_, v_a_2634_);
lean_dec(v_a_2634_);
v___x_2643_ = l_Array_append___redArg(v___x_2642_, v_a_2638_);
lean_dec(v_a_2638_);
v___x_2644_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v_a_2624_);
lean_ctor_set(v___x_2644_, 2, v_a_2632_);
lean_ctor_set(v___x_2644_, 3, v_a_2628_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2644_);
v___x_2646_ = v___x_2640_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_a_2634_);
lean_dec(v_a_2632_);
lean_dec(v_a_2628_);
lean_dec(v_a_2626_);
lean_dec(v_a_2624_);
v_a_2649_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2637_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2637_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_a_2632_);
lean_dec(v_a_2628_);
lean_dec(v_a_2626_);
lean_dec(v_a_2624_);
v_a_2657_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2633_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2633_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_a_2628_);
lean_dec(v_a_2626_);
lean_dec(v_a_2624_);
lean_dec_ref(v_indVal_2615_);
lean_dec(v_className_2613_);
v_a_2665_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2631_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2631_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_a_2624_);
lean_dec_ref(v_indVal_2615_);
lean_dec(v_className_2613_);
v_a_2673_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2625_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2625_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v_indVal_2615_);
lean_dec(v_className_2613_);
v_a_2681_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2623_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2623_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader___boxed(lean_object* v_className_2689_, lean_object* v_arity_2690_, lean_object* v_indVal_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Elab_Deriving_mkHeader(v_className_2689_, v_arity_2690_, v_indVal_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_arity_2690_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(lean_object* v_a_2700_, size_t v_sz_2701_, size_t v_i_2702_, lean_object* v_bs_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2700_, v_sz_2701_, v_i_2702_, v_bs_2703_, v___y_2708_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(lean_object* v_a_2712_, lean_object* v_sz_2713_, lean_object* v_i_2714_, lean_object* v_bs_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
size_t v_sz_boxed_2723_; size_t v_i_boxed_2724_; lean_object* v_res_2725_; 
v_sz_boxed_2723_ = lean_unbox_usize(v_sz_2713_);
lean_dec(v_sz_2713_);
v_i_boxed_2724_ = lean_unbox_usize(v_i_2714_);
lean_dec(v_i_2714_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_2712_, v_sz_boxed_2723_, v_i_boxed_2724_, v_bs_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(lean_object* v_upperBound_2726_, lean_object* v_inst_2727_, lean_object* v_R_2728_, lean_object* v_a_2729_, lean_object* v_b_2730_, lean_object* v_c_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2726_, v_a_2729_, v_b_2730_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___boxed(lean_object* v_upperBound_2740_, lean_object* v_inst_2741_, lean_object* v_R_2742_, lean_object* v_a_2743_, lean_object* v_b_2744_, lean_object* v_c_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(v_upperBound_2740_, v_inst_2741_, v_R_2742_, v_a_2743_, v_b_2744_, v_c_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v_upperBound_2740_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(lean_object* v_a_2754_, lean_object* v_b_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_array_2758_; lean_object* v_start_2759_; lean_object* v_stop_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2784_; 
v_array_2758_ = lean_ctor_get(v_a_2754_, 0);
v_start_2759_ = lean_ctor_get(v_a_2754_, 1);
v_stop_2760_ = lean_ctor_get(v_a_2754_, 2);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_a_2754_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2762_ = v_a_2754_;
v_isShared_2763_ = v_isSharedCheck_2784_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_stop_2760_);
lean_inc(v_start_2759_);
lean_inc(v_array_2758_);
lean_dec(v_a_2754_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2784_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_nat_dec_lt(v_start_2759_, v_stop_2760_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
lean_del_object(v___x_2762_);
lean_dec(v_stop_2760_);
lean_dec(v_start_2759_);
lean_dec_ref(v_array_2758_);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_b_2755_);
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_array_fget_borrowed(v_array_2758_, v_start_2759_);
lean_inc(v___x_2766_);
v___x_2767_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v___x_2766_, v___y_2756_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = lean_unsigned_to_nat(1u);
v___x_2770_ = lean_nat_add(v_start_2759_, v___x_2769_);
lean_dec(v_start_2759_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v___x_2770_);
v___x_2772_ = v___x_2762_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_array_2758_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_stop_2760_);
v___x_2772_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_array_push(v_b_2755_, v_a_2768_);
v_a_2754_ = v___x_2772_;
v_b_2755_ = v___x_2773_;
goto _start;
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_del_object(v___x_2762_);
lean_dec(v_stop_2760_);
lean_dec(v_start_2759_);
lean_dec_ref(v_array_2758_);
lean_dec_ref(v_b_2755_);
v_a_2776_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2767_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2767_);
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
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg___boxed(lean_object* v_a_2785_, lean_object* v_b_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2785_, v_b_2786_, v___y_2787_);
lean_dec_ref(v___y_2787_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(size_t v_sz_2790_, size_t v_i_2791_, lean_object* v_bs_2792_, lean_object* v___y_2793_){
_start:
{
uint8_t v___x_2795_; 
v___x_2795_ = lean_usize_dec_lt(v_i_2791_, v_sz_2790_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_bs_2792_);
return v___x_2796_;
}
else
{
lean_object* v_v_2797_; lean_object* v___x_2798_; 
v_v_2797_ = lean_array_uget_borrowed(v_bs_2792_, v_i_2791_);
lean_inc(v_v_2797_);
v___x_2798_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_v_2797_, v___y_2793_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v_bs_x27_2801_; size_t v___x_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = lean_unsigned_to_nat(0u);
v_bs_x27_2801_ = lean_array_uset(v_bs_2792_, v_i_2791_, v___x_2800_);
v___x_2802_ = ((size_t)1ULL);
v___x_2803_ = lean_usize_add(v_i_2791_, v___x_2802_);
v___x_2804_ = lean_array_uset(v_bs_x27_2801_, v_i_2791_, v_a_2799_);
v_i_2791_ = v___x_2803_;
v_bs_2792_ = v___x_2804_;
goto _start;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v_bs_2792_);
v_a_2806_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2798_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2798_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg___boxed(lean_object* v_sz_2814_, lean_object* v_i_2815_, lean_object* v_bs_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
size_t v_sz_boxed_2819_; size_t v_i_boxed_2820_; lean_object* v_res_2821_; 
v_sz_boxed_2819_ = lean_unbox_usize(v_sz_2814_);
lean_dec(v_sz_2814_);
v_i_boxed_2820_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_boxed_2819_, v_i_boxed_2820_, v_bs_2816_, v___y_2817_);
lean_dec_ref(v___y_2817_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object* v_header_2822_, lean_object* v_indVal_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_argNames_2831_; lean_object* v_targetNames_2832_; lean_object* v_numParams_2833_; lean_object* v___x_2834_; lean_object* v_discrs_2835_; lean_object* v_lower_2837_; lean_object* v_upper_2838_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_argNames_2831_ = lean_ctor_get(v_header_2822_, 1);
lean_inc_ref(v_argNames_2831_);
v_targetNames_2832_ = lean_ctor_get(v_header_2822_, 2);
lean_inc_ref(v_targetNames_2832_);
lean_dec_ref(v_header_2822_);
v_numParams_2833_ = lean_ctor_get(v_indVal_2823_, 1);
lean_inc(v_numParams_2833_);
lean_dec_ref(v_indVal_2823_);
v___x_2834_ = lean_unsigned_to_nat(0u);
v_discrs_2835_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2854_ = lean_array_get_size(v_argNames_2831_);
v___x_2855_ = lean_nat_dec_le(v_numParams_2833_, v___x_2834_);
if (v___x_2855_ == 0)
{
v_lower_2837_ = v_numParams_2833_;
v_upper_2838_ = v___x_2854_;
goto v___jp_2836_;
}
else
{
lean_dec(v_numParams_2833_);
v_lower_2837_ = v___x_2834_;
v_upper_2838_ = v___x_2854_;
goto v___jp_2836_;
}
v___jp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = l_Array_toSubarray___redArg(v_argNames_2831_, v_lower_2837_, v_upper_2838_);
v___x_2840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v___x_2839_, v_discrs_2835_, v_a_2828_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; size_t v_sz_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2840_, 1);
v_sz_2842_ = lean_array_size(v_targetNames_2832_);
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2842_, v___x_2843_, v_targetNames_2832_, v_a_2828_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2853_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = l_Array_append___redArg(v_a_2841_, v_a_2845_);
lean_dec(v_a_2845_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
else
{
lean_dec(v_a_2841_);
return v___x_2844_;
}
}
else
{
lean_dec_ref(v_targetNames_2832_);
return v___x_2840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs___boxed(lean_object* v_header_2856_, lean_object* v_indVal_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2856_, v_indVal_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(lean_object* v_inst_2866_, lean_object* v_R_2867_, lean_object* v_a_2868_, lean_object* v_b_2869_, lean_object* v_c_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2868_, v_b_2869_, v___y_2875_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(lean_object* v_inst_2879_, lean_object* v_R_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_, lean_object* v_c_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(v_inst_2879_, v_R_2880_, v_a_2881_, v_b_2882_, v_c_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(size_t v_sz_2892_, size_t v_i_2893_, lean_object* v_bs_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2892_, v_i_2893_, v_bs_2894_, v___y_2899_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(lean_object* v_sz_2903_, lean_object* v_i_2904_, lean_object* v_bs_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
size_t v_sz_boxed_2913_; size_t v_i_boxed_2914_; lean_object* v_res_2915_; 
v_sz_boxed_2913_ = lean_unbox_usize(v_sz_2903_);
lean_dec(v_sz_2903_);
v_i_boxed_2914_ = lean_unbox_usize(v_i_2904_);
lean_dec(v_i_2904_);
v_res_2915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_boxed_2913_, v_i_boxed_2914_, v_bs_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2915_;
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
