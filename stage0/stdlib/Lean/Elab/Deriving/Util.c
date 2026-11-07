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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_bs_1169_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1170_ == 0)
{
return v_bs_1169_;
}
else
{
lean_object* v_v_1171_; lean_object* v___x_1172_; lean_object* v_bs_x27_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v_v_1171_ = lean_array_uget(v_bs_1169_, v_i_1168_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v_bs_x27_1173_ = lean_array_uset(v_bs_1169_, v_i_1168_, v___x_1172_);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1168_, v___x_1174_);
v___x_1176_ = lean_array_uset(v_bs_x27_1173_, v_i_1168_, v_v_1171_);
v_i_1168_ = v___x_1175_;
v_bs_1169_ = v___x_1176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1___boxed(lean_object* v_sz_1178_, lean_object* v_i_1179_, lean_object* v_bs_1180_){
_start:
{
size_t v_sz_boxed_1181_; size_t v_i_boxed_1182_; lean_object* v_res_1183_; 
v_sz_boxed_1181_ = lean_unbox_usize(v_sz_1178_);
lean_dec(v_sz_1178_);
v_i_boxed_1182_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_boxed_1181_, v_i_boxed_1182_, v_bs_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(lean_object* v_msgData_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; uint8_t v___x_1192_; lean_object* v_env_1193_; lean_object* v___x_1194_; lean_object* v_toCold_1195_; lean_object* v_mctx_1196_; lean_object* v_lctx_1197_; lean_object* v_options_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1190_ = lean_st_ref_get(v___y_1188_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = 0;
v_env_1193_ = l_Lean_Environment_setRecordingDeps(v_env_1191_, v___x_1192_);
v___x_1194_ = lean_st_ref_get(v___y_1186_);
v_toCold_1195_ = lean_ctor_get(v___y_1187_, 0);
v_mctx_1196_ = lean_ctor_get(v___x_1194_, 0);
lean_inc_ref(v_mctx_1196_);
lean_dec(v___x_1194_);
v_lctx_1197_ = lean_ctor_get(v___y_1185_, 2);
v_options_1198_ = lean_ctor_get(v_toCold_1195_, 2);
lean_inc_ref(v_options_1198_);
lean_inc_ref(v_lctx_1197_);
v___x_1199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1199_, 0, v_env_1193_);
lean_ctor_set(v___x_1199_, 1, v_mctx_1196_);
lean_ctor_set(v___x_1199_, 2, v_lctx_1197_);
lean_ctor_set(v___x_1199_, 3, v_options_1198_);
v___x_1200_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_msgData_1184_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1209_, lean_object* v_macroStack_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1211_);
v___x_1214_ = l_Lean_Elab_pp_macroStack;
v___x_1215_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v___x_1213_, v___x_1214_);
lean_dec_ref(v___x_1213_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec(v_macroStack_1210_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_msgData_1209_);
return v___x_1216_;
}
else
{
if (lean_obj_tag(v_macroStack_1210_) == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_msgData_1209_);
return v___x_1217_;
}
else
{
lean_object* v_head_1218_; lean_object* v_after_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1234_; 
v_head_1218_ = lean_ctor_get(v_macroStack_1210_, 0);
lean_inc(v_head_1218_);
v_after_1219_ = lean_ctor_get(v_head_1218_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_head_1218_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_head_1218_, 0);
lean_dec(v_unused_1235_);
v___x_1221_ = v_head_1218_;
v_isShared_1222_ = v_isSharedCheck_1234_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_after_1219_);
lean_dec(v_head_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1234_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 7);
lean_ctor_set(v___x_1221_, 1, v___x_1223_);
lean_ctor_set(v___x_1221_, 0, v_msgData_1209_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_msgData_1209_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_msgData_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1226_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_MessageData_ofSyntax(v_after_1219_);
v___x_1229_ = l_Lean_indentD(v___x_1228_);
v_msgData_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1230_, 0, v___x_1227_);
lean_ctor_set(v_msgData_1230_, 1, v___x_1229_);
v___x_1231_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_1230_, v_macroStack_1210_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1236_, lean_object* v_macroStack_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1236_, v_macroStack_1237_, v___y_1238_);
lean_dec_ref(v___y_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(lean_object* v_msg_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_ref_1249_; lean_object* v_macroStack_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1263_; 
v_ref_1249_ = lean_ctor_get(v___y_1246_, 2);
v_macroStack_1250_ = lean_ctor_get(v___y_1242_, 1);
v___x_1251_ = l_Lean_Elab_getBetterRef(v_ref_1249_, v_macroStack_1250_);
v___x_1252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1241_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1252_);
lean_inc(v_macroStack_1250_);
v___x_1254_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_a_1253_, v_macroStack_1250_, v___y_1246_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1251_);
lean_ctor_set(v___x_1259_, 1, v_a_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(lean_object* v_constName_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v_env_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_st_ref_get(v___y_1279_);
v_env_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_ref(v_env_1282_);
lean_dec(v___x_1281_);
lean_inc(v_constName_1273_);
v___x_1283_ = l_Lean_isInductiveCore_x3f(v_env_1282_, v_constName_1273_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1284_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_1285_ = 0;
v___x_1286_ = l_Lean_MessageData_ofConstName(v_constName_1273_, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1284_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v___x_1289_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1290_;
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_constName_1273_);
v_val_1291_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1283_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v___x_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 0);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_val_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0___boxed(lean_object* v_constName_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_constName_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object* v_className_1309_, lean_object* v_indName_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_indName_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_n(v_a_1319_, 2);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_1319_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_n(v_a_1321_, 2);
lean_dec_ref_known(v___x_1320_, 1);
v___x_1322_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_1321_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v_ref_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_1319_, v_a_1321_, v_a_1315_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1324_);
v_ref_1326_ = lean_ctor_get(v_a_1315_, 2);
v___x_1327_ = 0;
v___x_1328_ = l_Lean_SourceInfo_fromRef(v_ref_1326_, v___x_1327_);
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
v___x_1330_ = l_Lean_mkCIdent(v_className_1309_);
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1328_);
v___x_1332_ = l_Lean_Syntax_node1(v___x_1328_, v___x_1331_, v_a_1325_);
v___x_1333_ = l_Lean_Syntax_node2(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstName___closed__0));
v_sz_1335_ = lean_array_size(v_a_1323_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_1335_, v___x_1336_, v_a_1323_);
v___x_1338_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_1334_, v___x_1337_, v___x_1333_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
return v___x_1338_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_a_1321_);
lean_dec(v_a_1319_);
lean_dec(v_className_1309_);
v_a_1339_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1322_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1322_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1319_);
lean_dec(v_className_1309_);
v_a_1347_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1320_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1320_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_className_1309_);
v_a_1355_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1318_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1318_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName___boxed(lean_object* v_className_1363_, lean_object* v_indName_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Elab_Deriving_mkInstName(v_className_1363_, v_indName_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(lean_object* v_00_u03b1_1373_, lean_object* v_msg_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_msg_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(v_00_u03b1_1383_, v_msg_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(lean_object* v_msgData_1393_, lean_object* v_macroStack_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1393_, v_macroStack_1394_, v___y_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1403_, lean_object* v_macroStack_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_1403_, v_macroStack_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(lean_object* v_as_x27_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
if (lean_obj_tag(v_as_x27_1413_) == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_b_1414_);
return v___x_1422_;
}
else
{
lean_object* v_head_1423_; lean_object* v_tail_1424_; lean_object* v___x_1425_; 
v_head_1423_ = lean_ctor_get(v_as_x27_1413_, 0);
v_tail_1424_ = lean_ctor_get(v_as_x27_1413_, 1);
lean_inc(v_head_1423_);
v___x_1425_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_head_1423_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = lean_array_push(v_b_1414_, v_a_1426_);
v_as_x27_1413_ = v_tail_1424_;
v_b_1414_ = v___x_1427_;
goto _start;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_b_1414_);
v_a_1429_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1425_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1425_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg___boxed(lean_object* v_as_x27_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1437_, v_b_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_as_x27_1437_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
if (lean_obj_tag(v_a_1447_) == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = l_List_reverse___redArg(v_a_1448_);
return v___x_1449_;
}
else
{
lean_object* v_head_1450_; lean_object* v_tail_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v_head_1450_ = lean_ctor_get(v_a_1447_, 0);
v_tail_1451_ = lean_ctor_get(v_a_1447_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1447_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v_a_1447_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_tail_1451_);
lean_inc(v_head_1450_);
lean_dec(v_a_1447_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = l_Lean_MessageData_ofName(v_head_1450_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_a_1448_);
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_a_1448_);
v___x_1457_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
v_a_1447_ = v_tail_1451_;
v_a_1448_ = v___x_1457_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1461_; double v___x_1462_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_float_of_nat(v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(lean_object* v_cls_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_ref_1473_; lean_object* v___x_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1520_; 
v_ref_1473_ = lean_ctor_get(v___y_1470_, 2);
v___x_1474_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1520_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1520_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v_traceState_1480_; lean_object* v_env_1481_; lean_object* v_nextMacroScope_1482_; lean_object* v_ngen_1483_; lean_object* v_auxDeclNGen_1484_; lean_object* v_cache_1485_; lean_object* v_recordedDeps_1486_; lean_object* v_messages_1487_; lean_object* v_infoState_1488_; lean_object* v_snapshotTasks_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1519_; 
v___x_1479_ = lean_st_ref_take(v___y_1471_);
v_traceState_1480_ = lean_ctor_get(v___x_1479_, 4);
v_env_1481_ = lean_ctor_get(v___x_1479_, 0);
v_nextMacroScope_1482_ = lean_ctor_get(v___x_1479_, 1);
v_ngen_1483_ = lean_ctor_get(v___x_1479_, 2);
v_auxDeclNGen_1484_ = lean_ctor_get(v___x_1479_, 3);
v_cache_1485_ = lean_ctor_get(v___x_1479_, 5);
v_recordedDeps_1486_ = lean_ctor_get(v___x_1479_, 6);
v_messages_1487_ = lean_ctor_get(v___x_1479_, 7);
v_infoState_1488_ = lean_ctor_get(v___x_1479_, 8);
v_snapshotTasks_1489_ = lean_ctor_get(v___x_1479_, 9);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1491_ = v___x_1479_;
v_isShared_1492_ = v_isSharedCheck_1519_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snapshotTasks_1489_);
lean_inc(v_infoState_1488_);
lean_inc(v_messages_1487_);
lean_inc(v_recordedDeps_1486_);
lean_inc(v_cache_1485_);
lean_inc(v_traceState_1480_);
lean_inc(v_auxDeclNGen_1484_);
lean_inc(v_ngen_1483_);
lean_inc(v_nextMacroScope_1482_);
lean_inc(v_env_1481_);
lean_dec(v___x_1479_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1519_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint64_t v_tid_1493_; lean_object* v_traces_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1518_; 
v_tid_1493_ = lean_ctor_get_uint64(v_traceState_1480_, sizeof(void*)*1);
v_traces_1494_ = lean_ctor_get(v_traceState_1480_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_traceState_1480_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1496_ = v_traceState_1480_;
v_isShared_1497_ = v_isSharedCheck_1518_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_traces_1494_);
lean_dec(v_traceState_1480_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1518_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; double v___x_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0);
v___x_1501_ = 0;
v___x_1502_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1));
v___x_1503_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1503_, 0, v_cls_1466_);
lean_ctor_set(v___x_1503_, 1, v___x_1499_);
lean_ctor_set(v___x_1503_, 2, v___x_1502_);
lean_ctor_set_float(v___x_1503_, sizeof(void*)*3, v___x_1500_);
lean_ctor_set_float(v___x_1503_, sizeof(void*)*3 + 8, v___x_1500_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*3 + 16, v___x_1501_);
v___x_1504_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2));
v___x_1505_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v_a_1475_);
lean_ctor_set(v___x_1505_, 2, v___x_1504_);
lean_inc(v_ref_1473_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_ref_1473_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_PersistentArray_push___redArg(v_traces_1494_, v___x_1506_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1507_);
v___x_1509_ = v___x_1496_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1507_);
lean_ctor_set_uint64(v_reuseFailAlloc_1517_, sizeof(void*)*1, v_tid_1493_);
v___x_1509_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v___x_1509_);
v___x_1511_ = v___x_1491_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_env_1481_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_nextMacroScope_1482_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_ngen_1483_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_auxDeclNGen_1484_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1516_, 5, v_cache_1485_);
lean_ctor_set(v_reuseFailAlloc_1516_, 6, v_recordedDeps_1486_);
lean_ctor_set(v_reuseFailAlloc_1516_, 7, v_messages_1487_);
lean_ctor_set(v_reuseFailAlloc_1516_, 8, v_infoState_1488_);
lean_ctor_set(v_reuseFailAlloc_1516_, 9, v_snapshotTasks_1489_);
v___x_1511_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_st_ref_put(v___y_1471_, v___x_1511_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1498_);
v___x_1514_ = v___x_1477_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1498_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___boxed(lean_object* v_cls_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1521_, v_msg_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(lean_object* v_fnPrefix_1530_, lean_object* v_a_1531_, lean_object* v_range_1532_, lean_object* v_b_1533_, lean_object* v_i_1534_){
_start:
{
lean_object* v_stop_1536_; lean_object* v_step_1537_; uint8_t v___x_1538_; 
v_stop_1536_ = lean_ctor_get(v_range_1532_, 1);
v_step_1537_ = lean_ctor_get(v_range_1532_, 2);
v___x_1538_ = lean_nat_dec_lt(v_i_1534_, v_stop_1536_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_dec(v_i_1534_);
lean_dec(v_a_1531_);
lean_dec_ref(v_fnPrefix_1530_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_b_1533_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0));
lean_inc_ref(v_fnPrefix_1530_);
v___x_1542_ = lean_string_append(v_fnPrefix_1530_, v___x_1541_);
v___x_1543_ = lean_nat_add(v_i_1534_, v___x_1540_);
v___x_1544_ = l_Nat_reprFast(v___x_1543_);
v___x_1545_ = lean_string_append(v___x_1542_, v___x_1544_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Lean_Name_str___override(v___x_1546_, v___x_1545_);
lean_inc(v_a_1531_);
v___x_1548_ = l_Lean_Name_append(v_a_1531_, v___x_1547_);
v___x_1549_ = lean_array_push(v_b_1533_, v___x_1548_);
v___x_1550_ = lean_nat_add(v_i_1534_, v_step_1537_);
lean_dec(v_i_1534_);
v_b_1533_ = v___x_1549_;
v_i_1534_ = v___x_1550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___boxed(lean_object* v_fnPrefix_1552_, lean_object* v_a_1553_, lean_object* v_range_1554_, lean_object* v_b_1555_, lean_object* v_i_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1552_, v_a_1553_, v_range_1554_, v_b_1555_, v_i_1556_);
lean_dec_ref(v_range_1554_);
return v_res_1558_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__5(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1568_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__4));
v___x_1569_ = l_Lean_Name_append(v___x_1568_, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__7(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__6));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__9(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__8));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext(lean_object* v_className_1576_, lean_object* v_fnPrefix_1577_, lean_object* v_typeName_1578_, uint8_t v_supportsRec_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
lean_inc(v_typeName_1578_);
v___x_1587_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_typeName_1578_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v_all_1589_; uint8_t v_isRec_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_all_1589_ = lean_ctor_get(v_a_1588_, 3);
v_isRec_1590_ = lean_ctor_get_uint8(v_a_1588_, sizeof(void*)*6);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1593_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_all_1589_, v___x_1592_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = l_Lean_Elab_Deriving_mkInstName(v_className_1576_, v_typeName_1578_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1657_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1657_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1657_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___y_1601_; uint8_t v___y_1602_; lean_object* v___y_1608_; lean_object* v_auxFunNames_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = l_List_lengthTR___redArg(v_all_1589_);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_dec_eq(v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_a_1652_; 
v___x_1650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1591_);
lean_ctor_set(v___x_1650_, 1, v___x_1647_);
lean_ctor_set(v___x_1650_, 2, v___x_1648_);
lean_inc(v_a_1596_);
v___x_1651_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1577_, v_a_1596_, v___x_1650_, v___x_1592_, v___x_1591_);
lean_dec_ref_known(v___x_1650_, 3);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref(v___x_1651_);
v_auxFunNames_1614_ = v_a_1652_;
v___y_1615_ = v_a_1580_;
v___y_1616_ = v_a_1581_;
v___y_1617_ = v_a_1582_;
v___y_1618_ = v_a_1583_;
v___y_1619_ = v_a_1584_;
v___y_1620_ = v_a_1585_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec(v___x_1647_);
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Lean_Name_str___override(v___x_1653_, v_fnPrefix_1577_);
lean_inc(v_a_1596_);
v___x_1655_ = l_Lean_Name_append(v_a_1596_, v___x_1654_);
v___x_1656_ = lean_array_push(v___x_1592_, v___x_1655_);
v_auxFunNames_1614_ = v___x_1656_;
v___y_1615_ = v_a_1580_;
v___y_1616_ = v_a_1581_;
v___y_1617_ = v_a_1582_;
v___y_1618_ = v_a_1583_;
v___y_1619_ = v_a_1584_;
v___y_1620_ = v_a_1585_;
goto v___jp_1613_;
}
v___jp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1603_, 0, v_a_1596_);
lean_ctor_set(v___x_1603_, 1, v_a_1594_);
lean_ctor_set(v___x_1603_, 2, v___y_1601_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*3, v___y_1602_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1603_);
v___x_1605_ = v___x_1598_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
v___jp_1607_:
{
uint8_t v___x_1609_; 
v___x_1609_ = l_Lean_InductiveVal_isNested(v_a_1588_);
lean_dec(v_a_1588_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_array_get_size(v_a_1594_);
v___x_1612_ = lean_nat_dec_lt(v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
if (v_isRec_1590_ == 0)
{
v___y_1601_ = v___y_1608_;
v___y_1602_ = v_isRec_1590_;
goto v___jp_1600_;
}
else
{
if (v_supportsRec_1579_ == 0)
{
v___y_1601_ = v___y_1608_;
v___y_1602_ = v_isRec_1590_;
goto v___jp_1600_;
}
else
{
v___y_1601_ = v___y_1608_;
v___y_1602_ = v___x_1612_;
goto v___jp_1600_;
}
}
}
else
{
v___y_1601_ = v___y_1608_;
v___y_1602_ = v___x_1612_;
goto v___jp_1600_;
}
}
else
{
v___y_1601_ = v___y_1608_;
v___y_1602_ = v___x_1609_;
goto v___jp_1600_;
}
}
v___jp_1613_:
{
lean_object* v_toCold_1621_; lean_object* v_options_1622_; uint8_t v_hasTrace_1623_; 
v_toCold_1621_ = lean_ctor_get(v___y_1619_, 0);
v_options_1622_ = lean_ctor_get(v_toCold_1621_, 2);
v_hasTrace_1623_ = lean_ctor_get_uint8(v_options_1622_, sizeof(void*)*1);
if (v_hasTrace_1623_ == 0)
{
v___y_1608_ = v_auxFunNames_1614_;
goto v___jp_1607_;
}
else
{
lean_object* v_inheritedTraceOptions_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v_inheritedTraceOptions_1624_ = lean_ctor_get(v_toCold_1621_, 11);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1626_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__5, &l_Lean_Elab_Deriving_mkContext___closed__5_once, _init_l_Lean_Elab_Deriving_mkContext___closed__5);
v___x_1627_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1624_, v_options_1622_, v___x_1626_);
if (v___x_1627_ == 0)
{
v___y_1608_ = v_auxFunNames_1614_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1628_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__7, &l_Lean_Elab_Deriving_mkContext___closed__7_once, _init_l_Lean_Elab_Deriving_mkContext___closed__7);
lean_inc(v_a_1596_);
v___x_1629_ = l_Lean_MessageData_ofName(v_a_1596_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__9, &l_Lean_Elab_Deriving_mkContext___closed__9_once, _init_l_Lean_Elab_Deriving_mkContext___closed__9);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
lean_inc_ref(v_auxFunNames_1614_);
v___x_1633_ = lean_array_to_list(v_auxFunNames_1614_);
v___x_1634_ = lean_box(0);
v___x_1635_ = l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(v___x_1633_, v___x_1634_);
v___x_1636_ = l_Lean_MessageData_ofList(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1632_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v___x_1625_, v___x_1637_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_dec_ref_known(v___x_1638_, 1);
v___y_1608_ = v_auxFunNames_1614_;
goto v___jp_1607_;
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v_auxFunNames_1614_);
lean_del_object(v___x_1598_);
lean_dec(v_a_1596_);
lean_dec(v_a_1594_);
lean_dec(v_a_1588_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
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
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1594_);
lean_dec(v_a_1588_);
lean_dec_ref(v_fnPrefix_1577_);
v_a_1658_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1595_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1595_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_a_1588_);
lean_dec(v_typeName_1578_);
lean_dec_ref(v_fnPrefix_1577_);
lean_dec(v_className_1576_);
v_a_1666_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1593_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1593_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_typeName_1578_);
lean_dec_ref(v_fnPrefix_1577_);
lean_dec(v_className_1576_);
v_a_1674_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1587_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1587_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object* v_className_1682_, lean_object* v_fnPrefix_1683_, lean_object* v_typeName_1684_, lean_object* v_supportsRec_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
uint8_t v_supportsRec_boxed_1693_; lean_object* v_res_1694_; 
v_supportsRec_boxed_1693_ = lean_unbox(v_supportsRec_1685_);
v_res_1694_ = l_Lean_Elab_Deriving_mkContext(v_className_1682_, v_fnPrefix_1683_, v_typeName_1684_, v_supportsRec_boxed_1693_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(lean_object* v_as_1695_, lean_object* v_as_x27_1696_, lean_object* v_b_1697_, lean_object* v_a_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1696_, v_b_1697_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___boxed(lean_object* v_as_1707_, lean_object* v_as_x27_1708_, lean_object* v_b_1709_, lean_object* v_a_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(v_as_1707_, v_as_x27_1708_, v_b_1709_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_as_x27_1708_);
lean_dec(v_as_1707_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(lean_object* v_cls_1719_, lean_object* v_msg_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1719_, v_msg_1720_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___boxed(lean_object* v_cls_1729_, lean_object* v_msg_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(v_cls_1729_, v_msg_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(lean_object* v_fnPrefix_1739_, lean_object* v_a_1740_, lean_object* v_range_1741_, lean_object* v_b_1742_, lean_object* v_i_1743_, lean_object* v_hs_1744_, lean_object* v_hl_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1739_, v_a_1740_, v_range_1741_, v_b_1742_, v_i_1743_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(lean_object* v_fnPrefix_1754_, lean_object* v_a_1755_, lean_object* v_range_1756_, lean_object* v_b_1757_, lean_object* v_i_1758_, lean_object* v_hs_1759_, lean_object* v_hl_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_1754_, v_a_1755_, v_range_1756_, v_b_1757_, v_i_1758_, v_hs_1759_, v_hl_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v_range_1756_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_1769_, lean_object* v_b_1770_){
_start:
{
lean_object* v_array_1771_; lean_object* v_start_1772_; lean_object* v_stop_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1786_; 
v_array_1771_ = lean_ctor_get(v_a_1769_, 0);
v_start_1772_ = lean_ctor_get(v_a_1769_, 1);
v_stop_1773_ = lean_ctor_get(v_a_1769_, 2);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_a_1769_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1775_ = v_a_1769_;
v_isShared_1776_ = v_isSharedCheck_1786_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_stop_1773_);
lean_inc(v_start_1772_);
lean_inc(v_array_1771_);
lean_dec(v_a_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1786_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_nat_dec_lt(v_start_1772_, v_stop_1773_);
if (v___x_1777_ == 0)
{
lean_del_object(v___x_1775_);
lean_dec(v_stop_1773_);
lean_dec(v_start_1772_);
lean_dec_ref(v_array_1771_);
return v_b_1770_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_start_1772_, v___x_1778_);
lean_inc_ref(v_array_1771_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1779_);
v___x_1781_ = v___x_1775_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_array_1771_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_stop_1773_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_array_fget(v_array_1771_, v_start_1772_);
lean_dec(v_start_1772_);
lean_dec_ref(v_array_1771_);
v___x_1783_ = lean_array_push(v_b_1770_, v___x_1782_);
v_a_1769_ = v___x_1781_;
v_b_1770_ = v___x_1783_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_ref_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_ref_1794_ = lean_ctor_get(v___y_1791_, 2);
v___x_1795_ = 0;
v___x_1796_ = l_Lean_SourceInfo_fromRef(v_ref_1794_, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(lean_object* v_upperBound_1843_, lean_object* v___x_1844_, lean_object* v_ctx_1845_, lean_object* v_argNames_1846_, lean_object* v_className_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_lt(v_a_1848_, v_upperBound_1843_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_b_1849_);
return v___x_1858_;
}
else
{
lean_object* v_auxFunNames_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_auxFunNames_1859_ = lean_ctor_get(v_ctx_1845_, 2);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_array_fget_borrowed(v___x_1844_, v_a_1848_);
v___x_1862_ = lean_array_get_borrowed(v___x_1860_, v_auxFunNames_1859_, v_a_1848_);
lean_inc(v___x_1861_);
v___x_1863_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_1861_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v_numParams_1865_; lean_object* v_lower_1867_; lean_object* v_upper_1868_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v_numParams_1865_ = lean_ctor_get(v___x_1861_, 1);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_array_get_size(v_a_1864_);
v___x_1962_ = lean_nat_dec_le(v_numParams_1865_, v___x_1960_);
if (v___x_1962_ == 0)
{
lean_inc(v_numParams_1865_);
v_lower_1867_ = v_numParams_1865_;
v_upper_1868_ = v___x_1961_;
goto v___jp_1866_;
}
else
{
v_lower_1867_ = v___x_1960_;
v_upper_1868_ = v___x_1961_;
goto v___jp_1866_;
}
v___jp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = l_Array_toSubarray___redArg(v_a_1864_, v_lower_1867_, v_upper_1868_);
lean_inc_ref(v___x_1869_);
v___x_1870_ = l_Subarray_copy___redArg(v___x_1869_);
v___x_1871_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_1870_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1865_);
lean_inc_ref(v_argNames_1846_);
v___x_1874_ = l_Array_toSubarray___redArg(v_argNames_1846_, v___x_1873_, v_numParams_1865_);
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_1876_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1874_, v___x_1875_);
v___x_1877_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1869_, v___x_1875_);
v_a_1878_ = l_Array_append___redArg(v___x_1876_, v___x_1877_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_array_get_size(v_a_1878_);
v___x_1880_ = l_Array_toSubarray___redArg(v_a_1878_, v___x_1873_, v___x_1879_);
v___x_1881_ = l_Subarray_copy___redArg(v___x_1880_);
lean_inc(v___x_1861_);
v___x_1882_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_1861_, v___x_1881_, v___y_1854_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_ref_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v_ref_1884_ = lean_ctor_get(v___y_1854_, 2);
v___x_1885_ = 0;
v___x_1886_ = l_Lean_SourceInfo_fromRef(v_ref_1884_, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_1847_);
v___x_1888_ = l_Lean_mkCIdent(v_className_1847_);
v___x_1889_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1886_);
v___x_1890_ = l_Lean_Syntax_node1(v___x_1886_, v___x_1889_, v_a_1883_);
v___x_1891_ = l_Lean_Syntax_node2(v___x_1886_, v___x_1887_, v___x_1888_, v___x_1890_);
v___x_1892_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_n(v_a_1893_, 4);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1));
v___x_1895_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_1896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1893_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
lean_inc(v___x_1862_);
v___x_1897_ = l_Lean_mkIdent(v___x_1862_);
v___x_1898_ = l_Lean_Syntax_node1(v_a_1893_, v___x_1889_, v___x_1897_);
v___x_1899_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_1900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_a_1893_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_Syntax_node3(v_a_1893_, v___x_1894_, v___x_1896_, v___x_1898_, v___x_1900_);
v___x_1902_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5));
v___x_1903_ = l_Lean_Core_mkFreshUserName(v___x_1902_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc_n(v_a_1906_, 8);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7));
v___x_1908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9));
v___x_1909_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11));
v___x_1910_ = l_Lean_mkIdent(v_a_1904_);
v___x_1911_ = l_Lean_Syntax_node1(v_a_1906_, v___x_1909_, v___x_1910_);
v___x_1912_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_1913_ = l_Array_append___redArg(v___x_1912_, v_a_1872_);
lean_dec(v_a_1872_);
v___x_1914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1906_);
lean_ctor_set(v___x_1914_, 1, v___x_1889_);
lean_ctor_set(v___x_1914_, 2, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13));
v___x_1916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_1917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1906_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_Syntax_node2(v_a_1906_, v___x_1915_, v___x_1917_, v___x_1891_);
v___x_1919_ = l_Lean_Syntax_node1(v_a_1906_, v___x_1889_, v___x_1918_);
v___x_1920_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_1921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_a_1906_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = l_Lean_Syntax_node5(v_a_1906_, v___x_1908_, v___x_1911_, v___x_1914_, v___x_1919_, v___x_1921_, v___x_1901_);
v___x_1923_ = l_Lean_Syntax_node1(v_a_1906_, v___x_1907_, v___x_1922_);
v___x_1924_ = lean_array_push(v_b_1849_, v___x_1923_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_add(v_a_1848_, v___x_1925_);
lean_dec(v_a_1848_);
v_a_1848_ = v___x_1926_;
v_b_1849_ = v___x_1924_;
goto _start;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1904_);
lean_dec(v___x_1901_);
lean_dec(v___x_1891_);
lean_dec(v_a_1872_);
lean_dec_ref(v_b_1849_);
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
v_a_1928_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1905_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1905_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v___x_1901_);
lean_dec(v___x_1891_);
lean_dec(v_a_1872_);
lean_dec_ref(v_b_1849_);
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
v_a_1936_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1903_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1903_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v___x_1891_);
lean_dec(v_a_1872_);
lean_dec_ref(v_b_1849_);
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
v_a_1944_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1892_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1892_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_a_1872_);
lean_dec_ref(v_b_1849_);
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
v_a_1952_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1882_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1882_);
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
else
{
lean_dec_ref(v___x_1869_);
lean_dec_ref(v_b_1849_);
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
return v___x_1871_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_b_1849_);
lean_dec(v_a_1848_);
lean_dec(v_className_1847_);
lean_dec_ref(v_argNames_1846_);
v_a_1963_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1863_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1863_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___boxed(lean_object* v_upperBound_1971_, lean_object* v___x_1972_, lean_object* v_ctx_1973_, lean_object* v_argNames_1974_, lean_object* v_className_1975_, lean_object* v_a_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_1971_, v___x_1972_, v_ctx_1973_, v_argNames_1974_, v_className_1975_, v_a_1976_, v_b_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec_ref(v_ctx_1973_);
lean_dec_ref(v___x_1972_);
lean_dec(v_upperBound_1971_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object* v_ctx_1986_, lean_object* v_className_1987_, lean_object* v_argNames_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_typeInfos_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v_letDecls_1999_; lean_object* v___x_2000_; 
v_typeInfos_1996_ = lean_ctor_get(v_ctx_1986_, 1);
v___x_1997_ = lean_array_get_size(v_typeInfos_1996_);
v___x_1998_ = lean_unsigned_to_nat(0u);
v_letDecls_1999_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v___x_1997_, v_typeInfos_1996_, v_ctx_1986_, v_argNames_1988_, v_className_1987_, v___x_1998_, v_letDecls_1999_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2001_, lean_object* v_className_2002_, lean_object* v_argNames_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2001_, v_className_2002_, v_argNames_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec_ref(v_ctx_2001_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2012_, lean_object* v_R_2013_, lean_object* v_a_2014_, lean_object* v_b_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2014_, v_b_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(lean_object* v_upperBound_2017_, lean_object* v___x_2018_, lean_object* v_ctx_2019_, lean_object* v_argNames_2020_, lean_object* v_className_2021_, lean_object* v_inst_2022_, lean_object* v_R_2023_, lean_object* v_a_2024_, lean_object* v_b_2025_, lean_object* v_c_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_2017_, v___x_2018_, v_ctx_2019_, v_argNames_2020_, v_className_2021_, v_a_2024_, v_b_2025_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2035_ = _args[0];
lean_object* v___x_2036_ = _args[1];
lean_object* v_ctx_2037_ = _args[2];
lean_object* v_argNames_2038_ = _args[3];
lean_object* v_className_2039_ = _args[4];
lean_object* v_inst_2040_ = _args[5];
lean_object* v_R_2041_ = _args[6];
lean_object* v_a_2042_ = _args[7];
lean_object* v_b_2043_ = _args[8];
lean_object* v_c_2044_ = _args[9];
lean_object* v___y_2045_ = _args[10];
lean_object* v___y_2046_ = _args[11];
lean_object* v___y_2047_ = _args[12];
lean_object* v___y_2048_ = _args[13];
lean_object* v___y_2049_ = _args[14];
lean_object* v___y_2050_ = _args[15];
lean_object* v___y_2051_ = _args[16];
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(v_upperBound_2035_, v___x_2036_, v_ctx_2037_, v_argNames_2038_, v_className_2039_, v_inst_2040_, v_R_2041_, v_a_2042_, v_b_2043_, v_c_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec_ref(v_ctx_2037_);
lean_dec_ref(v___x_2036_);
lean_dec(v_upperBound_2035_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(lean_object* v_as_2066_, size_t v_i_2067_, size_t v_stop_2068_, lean_object* v_b_2069_, lean_object* v___y_2070_){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_usize_dec_eq(v_i_2067_, v_stop_2068_);
if (v___x_2072_ == 0)
{
lean_object* v_ref_2073_; size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_ref_2073_ = lean_ctor_get(v___y_2070_, 2);
v___x_2074_ = ((size_t)1ULL);
v___x_2075_ = lean_usize_sub(v_i_2067_, v___x_2074_);
v___x_2076_ = lean_array_uget_borrowed(v_as_2066_, v___x_2075_);
v___x_2077_ = l_Lean_SourceInfo_fromRef(v_ref_2073_, v___x_2072_);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0));
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1));
lean_inc_n(v___x_2077_, 4);
v___x_2080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2077_);
lean_ctor_set(v___x_2080_, 1, v___x_2078_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3));
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2083_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2077_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
v___x_2085_ = l_Lean_Syntax_node1(v___x_2077_, v___x_2081_, v___x_2084_);
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4));
v___x_2087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2077_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
lean_inc(v___x_2076_);
v___x_2088_ = l_Lean_Syntax_node5(v___x_2077_, v___x_2079_, v___x_2080_, v___x_2085_, v___x_2076_, v___x_2087_, v_b_2069_);
v_i_2067_ = v___x_2075_;
v_b_2069_ = v___x_2088_;
goto _start;
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_b_2069_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
size_t v_i_boxed_2097_; size_t v_stop_boxed_2098_; lean_object* v_res_2099_; 
v_i_boxed_2097_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2098_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2091_, v_i_boxed_2097_, v_stop_boxed_2098_, v_b_2094_, v___y_2095_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_as_2091_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet(lean_object* v_letDecls_2100_, lean_object* v_body_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = lean_array_get_size(v_letDecls_2100_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_nat_dec_lt(v___x_2110_, v___x_2109_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_body_2101_);
return v___x_2112_;
}
else
{
size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_usize_of_nat(v___x_2109_);
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_letDecls_2100_, v___x_2113_, v___x_2114_, v_body_2101_, v_a_2106_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet___boxed(lean_object* v_letDecls_2116_, lean_object* v_body_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Elab_Deriving_mkLet(v_letDecls_2116_, v_body_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_letDecls_2116_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(lean_object* v_as_2126_, size_t v_i_2127_, size_t v_stop_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2126_, v_i_2127_, v_stop_2128_, v_b_2129_, v___y_2134_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(lean_object* v_as_2138_, lean_object* v_i_2139_, lean_object* v_stop_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
size_t v_i_boxed_2149_; size_t v_stop_boxed_2150_; lean_object* v_res_2151_; 
v_i_boxed_2149_ = lean_unbox_usize(v_i_2139_);
lean_dec(v_i_2139_);
v_stop_boxed_2150_ = lean_unbox_usize(v_stop_2140_);
lean_dec(v_stop_2140_);
v_res_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_2138_, v_i_boxed_2149_, v_stop_boxed_2150_, v_b_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec_ref(v_as_2138_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(lean_object* v___f_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v___x_2164_, lean_object* v___x_2165_, lean_object* v_instName_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_b_2169_, lean_object* v_____r_2170_, lean_object* v_val_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
lean_inc(v___y_2177_);
lean_inc_ref(v___y_2176_);
lean_inc(v___y_2175_);
lean_inc_ref(v___y_2174_);
lean_inc(v___y_2173_);
lean_inc_ref(v___y_2172_);
v___x_2179_ = lean_apply_7(v___f_2161_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, lean_box(0));
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2229_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2229_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2229_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0));
v___x_2185_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1));
lean_inc_ref_n(v___x_2163_, 8);
lean_inc_ref_n(v___x_2162_, 8);
v___x_2186_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2184_, v___x_2185_);
v___x_2187_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2));
v___x_2188_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2184_, v___x_2187_);
v___x_2189_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc_n(v___x_2164_, 2);
lean_inc_n(v_a_2180_, 14);
v___x_2190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2190_, 0, v_a_2180_);
lean_ctor_set(v___x_2190_, 1, v___x_2164_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_inc_ref_n(v___x_2190_, 12);
v___x_2191_ = l_Lean_Syntax_node7(v_a_2180_, v___x_2188_, v___x_2190_, v___x_2190_, v___x_2190_, v___x_2190_, v___x_2190_, v___x_2190_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3));
v___x_2193_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2184_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2));
lean_inc_ref(v___x_2165_);
v___x_2195_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2165_, v___x_2194_);
v___x_2196_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2195_, v___x_2190_);
v___x_2197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2180_);
lean_ctor_set(v___x_2197_, 1, v___x_2192_);
v___x_2198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4));
v___x_2199_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2184_, v___x_2198_);
v___x_2200_ = l_Lean_mkIdent(v_instName_2166_);
v___x_2201_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2199_, v___x_2200_, v___x_2190_);
v___x_2202_ = l_Lean_Syntax_node1(v_a_2180_, v___x_2164_, v___x_2201_);
v___x_2203_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5));
v___x_2204_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2184_, v___x_2203_);
v___x_2205_ = l_Array_append___redArg(v___x_2189_, v___x_2167_);
v___x_2206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2180_);
lean_ctor_set(v___x_2206_, 1, v___x_2164_);
lean_ctor_set(v___x_2206_, 2, v___x_2205_);
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12));
v___x_2208_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2165_, v___x_2207_);
v___x_2209_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2180_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2208_, v___x_2210_, v___x_2168_);
v___x_2212_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2204_, v___x_2206_, v___x_2211_);
v___x_2213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6));
v___x_2214_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2184_, v___x_2213_);
v___x_2215_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_2216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2180_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7));
v___x_2218_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8));
v___x_2219_ = l_Lean_Name_mkStr4(v___x_2162_, v___x_2163_, v___x_2217_, v___x_2218_);
v___x_2220_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2219_, v___x_2190_, v___x_2190_);
v___x_2221_ = l_Lean_Syntax_node4(v_a_2180_, v___x_2214_, v___x_2216_, v_val_2171_, v___x_2220_, v___x_2190_);
v___x_2222_ = l_Lean_Syntax_node6(v_a_2180_, v___x_2193_, v___x_2196_, v___x_2197_, v___x_2190_, v___x_2202_, v___x_2212_, v___x_2221_);
v___x_2223_ = l_Lean_Syntax_node2(v_a_2180_, v___x_2186_, v___x_2191_, v___x_2222_);
v___x_2224_ = lean_array_push(v_b_2169_, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2225_);
v___x_2227_ = v___x_2182_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_val_2171_);
lean_dec_ref(v_b_2169_);
lean_dec(v___x_2168_);
lean_dec(v_instName_2166_);
lean_dec_ref(v___x_2165_);
lean_dec(v___x_2164_);
lean_dec_ref(v___x_2163_);
lean_dec_ref(v___x_2162_);
v_a_2230_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2179_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2179_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___f_2238_ = _args[0];
lean_object* v___x_2239_ = _args[1];
lean_object* v___x_2240_ = _args[2];
lean_object* v___x_2241_ = _args[3];
lean_object* v___x_2242_ = _args[4];
lean_object* v_instName_2243_ = _args[5];
lean_object* v___x_2244_ = _args[6];
lean_object* v___x_2245_ = _args[7];
lean_object* v_b_2246_ = _args[8];
lean_object* v_____r_2247_ = _args[9];
lean_object* v_val_2248_ = _args[10];
lean_object* v___y_2249_ = _args[11];
lean_object* v___y_2250_ = _args[12];
lean_object* v___y_2251_ = _args[13];
lean_object* v___y_2252_ = _args[14];
lean_object* v___y_2253_ = _args[15];
lean_object* v___y_2254_ = _args[16];
lean_object* v___y_2255_ = _args[17];
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2238_, v___x_2239_, v___x_2240_, v___x_2241_, v___x_2242_, v_instName_2243_, v___x_2244_, v___x_2245_, v_b_2246_, v_____r_2247_, v_val_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v___x_2244_);
return v_res_2256_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_2257_, lean_object* v_as_2258_, size_t v_i_2259_, size_t v_stop_2260_){
_start:
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_usize_dec_eq(v_i_2259_, v_stop_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_array_uget_borrowed(v_as_2258_, v_i_2259_);
v___x_2263_ = lean_name_eq(v_a_2257_, v___x_2262_);
if (v___x_2263_ == 0)
{
size_t v___x_2264_; size_t v___x_2265_; 
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_add(v_i_2259_, v___x_2264_);
v_i_2259_ = v___x_2265_;
goto _start;
}
else
{
return v___x_2263_;
}
}
else
{
uint8_t v___x_2267_; 
v___x_2267_ = 0;
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_2268_, lean_object* v_as_2269_, lean_object* v_i_2270_, lean_object* v_stop_2271_){
_start:
{
size_t v_i_boxed_2272_; size_t v_stop_boxed_2273_; uint8_t v_res_2274_; lean_object* v_r_2275_; 
v_i_boxed_2272_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_stop_boxed_2273_ = lean_unbox_usize(v_stop_2271_);
lean_dec(v_stop_2271_);
v_res_2274_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2268_, v_as_2269_, v_i_boxed_2272_, v_stop_boxed_2273_);
lean_dec_ref(v_as_2269_);
lean_dec(v_a_2268_);
v_r_2275_ = lean_box(v_res_2274_);
return v_r_2275_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(lean_object* v_as_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_array_get_size(v_as_2276_);
v___x_2280_ = lean_nat_dec_lt(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
return v___x_2280_;
}
else
{
size_t v___x_2281_; size_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2281_ = ((size_t)0ULL);
v___x_2282_ = lean_usize_of_nat(v___x_2279_);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2277_, v_as_2276_, v___x_2281_, v___x_2282_);
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0___boxed(lean_object* v_as_2284_, lean_object* v_a_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_as_2284_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(lean_object* v_upperBound_2289_, lean_object* v___x_2290_, lean_object* v_typeNames_2291_, lean_object* v_ctx_2292_, lean_object* v_className_2293_, uint8_t v_useAnonCtor_2294_, lean_object* v_a_2295_, lean_object* v_b_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_a_2305_; lean_object* v___y_2310_; uint8_t v___x_2329_; 
v___x_2329_ = lean_nat_dec_lt(v_a_2295_, v_upperBound_2289_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_b_2296_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_toConstantVal_2333_; lean_object* v_name_2334_; uint8_t v___x_2335_; 
v___x_2331_ = l_Lean_instInhabitedInductiveVal_default;
v___x_2332_ = lean_array_get_borrowed(v___x_2331_, v___x_2290_, v_a_2295_);
v_toConstantVal_2333_ = lean_ctor_get(v___x_2332_, 0);
v_name_2334_ = lean_ctor_get(v_toConstantVal_2333_, 0);
v___x_2335_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_typeNames_2291_, v_name_2334_);
if (v___x_2335_ == 0)
{
v_a_2305_ = v_b_2296_;
goto v___jp_2304_;
}
else
{
lean_object* v_instName_2336_; lean_object* v_auxFunNames_2337_; lean_object* v___f_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_instName_2336_ = lean_ctor_get(v_ctx_2292_, 0);
v_auxFunNames_2337_ = lean_ctor_get(v_ctx_2292_, 2);
v___f_2338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0));
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_array_get_borrowed(v___x_2339_, v_auxFunNames_2337_, v_a_2295_);
lean_inc(v___x_2332_);
v___x_2341_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_2332_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_n(v_a_2342_, 2);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2342_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
lean_inc(v_a_2342_);
lean_inc(v___x_2332_);
lean_inc(v_className_2293_);
v___x_2345_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2293_, v___x_2332_, v_a_2342_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0));
v___x_2348_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1));
v___x_2349_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2));
v___x_2350_ = l_Array_append___redArg(v_a_2344_, v_a_2346_);
lean_dec(v_a_2346_);
lean_inc(v___x_2332_);
v___x_2351_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_2332_, v_a_2342_, v___y_2301_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v_ref_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_ref_2353_ = lean_ctor_get(v___y_2301_, 2);
v___x_2354_ = 0;
v___x_2355_ = l_Lean_SourceInfo_fromRef(v_ref_2353_, v___x_2354_);
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_2293_);
v___x_2357_ = l_Lean_mkCIdent(v_className_2293_);
v___x_2358_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_2355_);
v___x_2359_ = l_Lean_Syntax_node1(v___x_2355_, v___x_2358_, v_a_2352_);
v___x_2360_ = l_Lean_Syntax_node2(v___x_2355_, v___x_2356_, v___x_2357_, v___x_2359_);
lean_inc(v___x_2340_);
v___x_2361_ = l_Lean_mkIdent(v___x_2340_);
if (v_useAnonCtor_2294_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_box(0);
lean_inc(v_instName_2336_);
v___x_2363_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2338_, v___x_2347_, v___x_2348_, v___x_2358_, v___x_2349_, v_instName_2336_, v___x_2350_, v___x_2360_, v_b_2296_, v___x_2362_, v___x_2361_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec_ref(v___x_2350_);
v___y_2310_ = v___x_2363_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_n(v_a_2365_, 4);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1));
v___x_2367_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_2368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_a_2365_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = l_Lean_Syntax_node1(v_a_2365_, v___x_2358_, v___x_2361_);
v___x_2370_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_2371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2365_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_Syntax_node3(v_a_2365_, v___x_2366_, v___x_2368_, v___x_2369_, v___x_2371_);
v___x_2373_ = lean_box(0);
lean_inc(v_instName_2336_);
v___x_2374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2338_, v___x_2347_, v___x_2348_, v___x_2358_, v___x_2349_, v_instName_2336_, v___x_2350_, v___x_2360_, v_b_2296_, v___x_2373_, v___x_2372_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec_ref(v___x_2350_);
v___y_2310_ = v___x_2374_;
goto v___jp_2309_;
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v___x_2361_);
lean_dec(v___x_2360_);
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_b_2296_);
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v_a_2375_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2364_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2364_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_b_2296_);
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v_a_2383_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2351_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2351_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_a_2344_);
lean_dec(v_a_2342_);
lean_dec_ref(v_b_2296_);
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v_a_2391_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2345_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2345_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_dec(v_a_2342_);
lean_dec_ref(v_b_2296_);
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
return v___x_2343_;
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_b_2296_);
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v_a_2399_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2341_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2341_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
v___jp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = lean_nat_add(v_a_2295_, v___x_2306_);
lean_dec(v_a_2295_);
v_a_2295_ = v___x_2307_;
v_b_2296_ = v_a_2305_;
goto _start;
}
v___jp_2309_:
{
if (lean_obj_tag(v___y_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2320_; 
v_a_2311_ = lean_ctor_get(v___y_2310_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___y_2310_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2313_ = v___y_2310_;
v_isShared_2314_ = v_isSharedCheck_2320_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___y_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2320_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
if (lean_obj_tag(v_a_2311_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; 
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v_a_2315_ = lean_ctor_get(v_a_2311_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v_a_2311_, 1);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v_a_2315_);
v___x_2317_ = v___x_2313_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
else
{
lean_object* v_a_2319_; 
lean_del_object(v___x_2313_);
v_a_2319_ = lean_ctor_get(v_a_2311_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v_a_2311_, 1);
v_a_2305_ = v_a_2319_;
goto v___jp_2304_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2295_);
lean_dec(v_className_2293_);
lean_dec_ref(v_ctx_2292_);
v_a_2321_ = lean_ctor_get(v___y_2310_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___y_2310_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___y_2310_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___y_2310_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_upperBound_2407_, lean_object* v___x_2408_, lean_object* v_typeNames_2409_, lean_object* v_ctx_2410_, lean_object* v_className_2411_, lean_object* v_useAnonCtor_2412_, lean_object* v_a_2413_, lean_object* v_b_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
uint8_t v_useAnonCtor_boxed_2422_; lean_object* v_res_2423_; 
v_useAnonCtor_boxed_2422_ = lean_unbox(v_useAnonCtor_2412_);
v_res_2423_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2407_, v___x_2408_, v_typeNames_2409_, v_ctx_2410_, v_className_2411_, v_useAnonCtor_boxed_2422_, v_a_2413_, v_b_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec_ref(v_typeNames_2409_);
lean_dec_ref(v___x_2408_);
lean_dec(v_upperBound_2407_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object* v_ctx_2424_, lean_object* v_className_2425_, lean_object* v_typeNames_2426_, uint8_t v_useAnonCtor_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_typeInfos_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_instances_2438_; lean_object* v___x_2439_; 
v_typeInfos_2435_ = lean_ctor_get(v_ctx_2424_, 1);
lean_inc_ref(v_typeInfos_2435_);
v___x_2436_ = lean_array_get_size(v_typeInfos_2435_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v_instances_2438_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v___x_2436_, v_typeInfos_2435_, v_typeNames_2426_, v_ctx_2424_, v_className_2425_, v_useAnonCtor_2427_, v___x_2437_, v_instances_2438_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec_ref(v_typeInfos_2435_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds___boxed(lean_object* v_ctx_2440_, lean_object* v_className_2441_, lean_object* v_typeNames_2442_, lean_object* v_useAnonCtor_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
uint8_t v_useAnonCtor_boxed_2451_; lean_object* v_res_2452_; 
v_useAnonCtor_boxed_2451_ = lean_unbox(v_useAnonCtor_2443_);
v_res_2452_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_2440_, v_className_2441_, v_typeNames_2442_, v_useAnonCtor_boxed_2451_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_typeNames_2442_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(lean_object* v_upperBound_2453_, lean_object* v___x_2454_, lean_object* v_typeNames_2455_, lean_object* v_ctx_2456_, lean_object* v_className_2457_, uint8_t v_useAnonCtor_2458_, lean_object* v_inst_2459_, lean_object* v_R_2460_, lean_object* v_a_2461_, lean_object* v_b_2462_, lean_object* v_c_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2453_, v___x_2454_, v_typeNames_2455_, v_ctx_2456_, v_className_2457_, v_useAnonCtor_2458_, v_a_2461_, v_b_2462_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2472_ = _args[0];
lean_object* v___x_2473_ = _args[1];
lean_object* v_typeNames_2474_ = _args[2];
lean_object* v_ctx_2475_ = _args[3];
lean_object* v_className_2476_ = _args[4];
lean_object* v_useAnonCtor_2477_ = _args[5];
lean_object* v_inst_2478_ = _args[6];
lean_object* v_R_2479_ = _args[7];
lean_object* v_a_2480_ = _args[8];
lean_object* v_b_2481_ = _args[9];
lean_object* v_c_2482_ = _args[10];
lean_object* v___y_2483_ = _args[11];
lean_object* v___y_2484_ = _args[12];
lean_object* v___y_2485_ = _args[13];
lean_object* v___y_2486_ = _args[14];
lean_object* v___y_2487_ = _args[15];
lean_object* v___y_2488_ = _args[16];
lean_object* v___y_2489_ = _args[17];
_start:
{
uint8_t v_useAnonCtor_boxed_2490_; lean_object* v_res_2491_; 
v_useAnonCtor_boxed_2490_ = lean_unbox(v_useAnonCtor_2477_);
v_res_2491_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(v_upperBound_2472_, v___x_2473_, v_typeNames_2474_, v_ctx_2475_, v_className_2476_, v_useAnonCtor_boxed_2490_, v_inst_2478_, v_R_2479_, v_a_2480_, v_b_2481_, v_c_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_typeNames_2474_);
lean_dec_ref(v___x_2473_);
lean_dec(v_upperBound_2472_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg(lean_object* v_varName_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_ref_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_ref_2501_ = lean_ctor_get(v_a_2499_, 2);
v___x_2502_ = 0;
v___x_2503_ = l_Lean_SourceInfo_fromRef(v_ref_2501_, v___x_2502_);
v___x_2504_ = ((lean_object*)(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1));
v___x_2505_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2506_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc(v___x_2503_);
v___x_2507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2503_);
lean_ctor_set(v___x_2507_, 1, v___x_2505_);
lean_ctor_set(v___x_2507_, 2, v___x_2506_);
v___x_2508_ = l_Lean_mkIdent(v_varName_2498_);
v___x_2509_ = l_Lean_Syntax_node2(v___x_2503_, v___x_2504_, v___x_2507_, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(lean_object* v_varName_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2511_, v_a_2512_);
lean_dec_ref(v_a_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr(lean_object* v_varName_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2515_, v_a_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___boxed(lean_object* v_varName_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Elab_Deriving_mkDiscr(v_varName_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(lean_object* v_upperBound_2536_, lean_object* v_a_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_nat_dec_lt(v_a_2537_, v_upperBound_2536_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
lean_dec(v_a_2537_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_b_2538_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1));
v___x_2545_ = l_Lean_Core_mkFreshUserName(v___x_2544_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = lean_array_push(v_b_2538_, v_a_2546_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v_a_2537_, v___x_2548_);
lean_dec(v_a_2537_);
v_a_2537_ = v___x_2549_;
v_b_2538_ = v___x_2547_;
goto _start;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_b_2538_);
lean_dec(v_a_2537_);
v_a_2551_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2545_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2545_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___boxed(lean_object* v_upperBound_2559_, lean_object* v_a_2560_, lean_object* v_b_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2559_, v_a_2560_, v_b_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v_upperBound_2559_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(lean_object* v_a_2574_, size_t v_sz_2575_, size_t v_i_2576_, lean_object* v_bs_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = lean_usize_dec_lt(v_i_2576_, v_sz_2575_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; 
lean_dec(v_a_2574_);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_bs_2577_);
return v___x_2581_;
}
else
{
lean_object* v_ref_2582_; lean_object* v_v_2583_; lean_object* v___x_2584_; lean_object* v_bs_x27_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v_ref_2582_ = lean_ctor_get(v___y_2578_, 2);
v_v_2583_ = lean_array_uget(v_bs_2577_, v_i_2576_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v_bs_x27_2585_ = lean_array_uset(v_bs_2577_, v_i_2576_, v___x_2584_);
v___x_2586_ = 0;
v___x_2587_ = l_Lean_SourceInfo_fromRef(v_ref_2582_, v___x_2586_);
v___x_2588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1));
v___x_2589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2));
lean_inc_n(v___x_2587_, 6);
v___x_2590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2587_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2592_ = l_Lean_mkIdent(v_v_2583_);
v___x_2593_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2591_, v___x_2592_);
v___x_2594_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2587_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_inc(v_a_2574_);
v___x_2596_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2591_, v___x_2595_, v_a_2574_);
v___x_2597_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2598_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2587_);
lean_ctor_set(v___x_2598_, 1, v___x_2591_);
lean_ctor_set(v___x_2598_, 2, v___x_2597_);
v___x_2599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3));
v___x_2600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2587_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = l_Lean_Syntax_node5(v___x_2587_, v___x_2588_, v___x_2590_, v___x_2593_, v___x_2596_, v___x_2598_, v___x_2600_);
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_add(v_i_2576_, v___x_2602_);
v___x_2604_ = lean_array_uset(v_bs_x27_2585_, v_i_2576_, v___x_2601_);
v_i_2576_ = v___x_2603_;
v_bs_2577_ = v___x_2604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___boxed(lean_object* v_a_2606_, lean_object* v_sz_2607_, lean_object* v_i_2608_, lean_object* v_bs_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
size_t v_sz_boxed_2612_; size_t v_i_boxed_2613_; lean_object* v_res_2614_; 
v_sz_boxed_2612_ = lean_unbox_usize(v_sz_2607_);
lean_dec(v_sz_2607_);
v_i_boxed_2613_ = lean_unbox_usize(v_i_2608_);
lean_dec(v_i_2608_);
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2606_, v_sz_boxed_2612_, v_i_boxed_2613_, v_bs_2609_, v___y_2610_);
lean_dec_ref(v___y_2610_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object* v_className_2615_, lean_object* v_arity_2616_, lean_object* v_indVal_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2625_; 
lean_inc_ref(v_indVal_2617_);
v___x_2625_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_n(v_a_2626_, 2);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2626_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
lean_inc(v_a_2626_);
lean_inc_ref(v_indVal_2617_);
v___x_2629_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_2617_, v_a_2626_, v_a_2622_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_2633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_arity_2616_, v___x_2631_, v___x_2632_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
lean_inc(v_a_2626_);
v___x_2635_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2615_, v_indVal_2617_, v_a_2626_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; size_t v_sz_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = l_Array_append___redArg(v_a_2628_, v_a_2636_);
lean_dec(v_a_2636_);
v_sz_2638_ = lean_array_size(v_a_2634_);
v___x_2639_ = ((size_t)0ULL);
lean_inc(v_a_2634_);
lean_inc(v_a_2630_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2630_, v_sz_2638_, v___x_2639_, v_a_2634_, v_a_2622_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2650_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = l_Array_append___redArg(v___x_2637_, v_a_2641_);
lean_dec(v_a_2641_);
v___x_2646_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v_a_2626_);
lean_ctor_set(v___x_2646_, 2, v_a_2634_);
lean_ctor_set(v___x_2646_, 3, v_a_2630_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref(v___x_2637_);
lean_dec(v_a_2634_);
lean_dec(v_a_2630_);
lean_dec(v_a_2626_);
v_a_2651_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2640_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2640_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_a_2634_);
lean_dec(v_a_2630_);
lean_dec(v_a_2628_);
lean_dec(v_a_2626_);
v_a_2659_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2635_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2635_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_a_2630_);
lean_dec(v_a_2628_);
lean_dec(v_a_2626_);
lean_dec_ref(v_indVal_2617_);
lean_dec(v_className_2615_);
v_a_2667_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2633_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2633_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2626_);
lean_dec_ref(v_indVal_2617_);
lean_dec(v_className_2615_);
v_a_2675_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2627_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2627_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_indVal_2617_);
lean_dec(v_className_2615_);
v_a_2683_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2625_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2625_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader___boxed(lean_object* v_className_2691_, lean_object* v_arity_2692_, lean_object* v_indVal_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_Elab_Deriving_mkHeader(v_className_2691_, v_arity_2692_, v_indVal_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_arity_2692_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(lean_object* v_a_2702_, size_t v_sz_2703_, size_t v_i_2704_, lean_object* v_bs_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2702_, v_sz_2703_, v_i_2704_, v_bs_2705_, v___y_2710_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(lean_object* v_a_2714_, lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_bs_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
size_t v_sz_boxed_2725_; size_t v_i_boxed_2726_; lean_object* v_res_2727_; 
v_sz_boxed_2725_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2726_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_2714_, v_sz_boxed_2725_, v_i_boxed_2726_, v_bs_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(lean_object* v_upperBound_2728_, lean_object* v_inst_2729_, lean_object* v_R_2730_, lean_object* v_a_2731_, lean_object* v_b_2732_, lean_object* v_c_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2728_, v_a_2731_, v_b_2732_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___boxed(lean_object* v_upperBound_2742_, lean_object* v_inst_2743_, lean_object* v_R_2744_, lean_object* v_a_2745_, lean_object* v_b_2746_, lean_object* v_c_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(v_upperBound_2742_, v_inst_2743_, v_R_2744_, v_a_2745_, v_b_2746_, v_c_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v_upperBound_2742_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(lean_object* v_a_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_array_2760_; lean_object* v_start_2761_; lean_object* v_stop_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2786_; 
v_array_2760_ = lean_ctor_get(v_a_2756_, 0);
v_start_2761_ = lean_ctor_get(v_a_2756_, 1);
v_stop_2762_ = lean_ctor_get(v_a_2756_, 2);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_a_2756_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2764_ = v_a_2756_;
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_stop_2762_);
lean_inc(v_start_2761_);
lean_inc(v_array_2760_);
lean_dec(v_a_2756_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2786_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
uint8_t v___x_2766_; 
v___x_2766_ = lean_nat_dec_lt(v_start_2761_, v_stop_2762_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
lean_del_object(v___x_2764_);
lean_dec(v_stop_2762_);
lean_dec(v_start_2761_);
lean_dec_ref(v_array_2760_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_b_2757_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2768_ = lean_unsigned_to_nat(1u);
v___x_2769_ = lean_nat_add(v_start_2761_, v___x_2768_);
lean_inc_ref(v_array_2760_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 1, v___x_2769_);
v___x_2771_ = v___x_2764_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_array_2760_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_stop_2762_);
v___x_2771_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_array_fget(v_array_2760_, v_start_2761_);
lean_dec(v_start_2761_);
lean_dec_ref(v_array_2760_);
v___x_2773_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v___x_2772_, v___y_2758_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = lean_array_push(v_b_2757_, v_a_2774_);
v_a_2756_ = v___x_2771_;
v_b_2757_ = v___x_2775_;
goto _start;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v___x_2771_);
lean_dec_ref(v_b_2757_);
v_a_2777_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2773_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg___boxed(lean_object* v_a_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2787_, v_b_2788_, v___y_2789_);
lean_dec_ref(v___y_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(size_t v_sz_2792_, size_t v_i_2793_, lean_object* v_bs_2794_, lean_object* v___y_2795_){
_start:
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_usize_dec_lt(v_i_2793_, v_sz_2792_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_bs_2794_);
return v___x_2798_;
}
else
{
lean_object* v_v_2799_; lean_object* v___x_2800_; lean_object* v_bs_x27_2801_; lean_object* v___x_2802_; 
v_v_2799_ = lean_array_uget(v_bs_2794_, v_i_2793_);
v___x_2800_ = lean_unsigned_to_nat(0u);
v_bs_x27_2801_ = lean_array_uset(v_bs_2794_, v_i_2793_, v___x_2800_);
v___x_2802_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_v_2799_, v___y_2795_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = ((size_t)1ULL);
v___x_2805_ = lean_usize_add(v_i_2793_, v___x_2804_);
v___x_2806_ = lean_array_uset(v_bs_x27_2801_, v_i_2793_, v_a_2803_);
v_i_2793_ = v___x_2805_;
v_bs_2794_ = v___x_2806_;
goto _start;
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v_bs_x27_2801_);
v_a_2808_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2802_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2802_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg___boxed(lean_object* v_sz_2816_, lean_object* v_i_2817_, lean_object* v_bs_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
size_t v_sz_boxed_2821_; size_t v_i_boxed_2822_; lean_object* v_res_2823_; 
v_sz_boxed_2821_ = lean_unbox_usize(v_sz_2816_);
lean_dec(v_sz_2816_);
v_i_boxed_2822_ = lean_unbox_usize(v_i_2817_);
lean_dec(v_i_2817_);
v_res_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_boxed_2821_, v_i_boxed_2822_, v_bs_2818_, v___y_2819_);
lean_dec_ref(v___y_2819_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object* v_header_2824_, lean_object* v_indVal_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_argNames_2833_; lean_object* v_targetNames_2834_; lean_object* v_numParams_2835_; lean_object* v___x_2836_; lean_object* v_discrs_2837_; lean_object* v_lower_2839_; lean_object* v_upper_2840_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_argNames_2833_ = lean_ctor_get(v_header_2824_, 1);
lean_inc_ref(v_argNames_2833_);
v_targetNames_2834_ = lean_ctor_get(v_header_2824_, 2);
lean_inc_ref(v_targetNames_2834_);
lean_dec_ref(v_header_2824_);
v_numParams_2835_ = lean_ctor_get(v_indVal_2825_, 1);
lean_inc(v_numParams_2835_);
lean_dec_ref(v_indVal_2825_);
v___x_2836_ = lean_unsigned_to_nat(0u);
v_discrs_2837_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2856_ = lean_array_get_size(v_argNames_2833_);
v___x_2857_ = lean_nat_dec_le(v_numParams_2835_, v___x_2836_);
if (v___x_2857_ == 0)
{
v_lower_2839_ = v_numParams_2835_;
v_upper_2840_ = v___x_2856_;
goto v___jp_2838_;
}
else
{
lean_dec(v_numParams_2835_);
v_lower_2839_ = v___x_2836_;
v_upper_2840_ = v___x_2856_;
goto v___jp_2838_;
}
v___jp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = l_Array_toSubarray___redArg(v_argNames_2833_, v_lower_2839_, v_upper_2840_);
v___x_2842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v___x_2841_, v_discrs_2837_, v_a_2830_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; size_t v_sz_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v_sz_2844_ = lean_array_size(v_targetNames_2834_);
v___x_2845_ = ((size_t)0ULL);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2844_, v___x_2845_, v_targetNames_2834_, v_a_2830_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2855_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2855_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2855_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2851_ = l_Array_append___redArg(v_a_2843_, v_a_2847_);
lean_dec(v_a_2847_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
else
{
lean_dec(v_a_2843_);
return v___x_2846_;
}
}
else
{
lean_dec_ref(v_targetNames_2834_);
return v___x_2842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs___boxed(lean_object* v_header_2858_, lean_object* v_indVal_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2858_, v_indVal_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(lean_object* v_inst_2868_, lean_object* v_R_2869_, lean_object* v_a_2870_, lean_object* v_b_2871_, lean_object* v_c_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2870_, v_b_2871_, v___y_2877_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(lean_object* v_inst_2881_, lean_object* v_R_2882_, lean_object* v_a_2883_, lean_object* v_b_2884_, lean_object* v_c_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(v_inst_2881_, v_R_2882_, v_a_2883_, v_b_2884_, v_c_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(size_t v_sz_2894_, size_t v_i_2895_, lean_object* v_bs_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2894_, v_i_2895_, v_bs_2896_, v___y_2901_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(lean_object* v_sz_2905_, lean_object* v_i_2906_, lean_object* v_bs_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
size_t v_sz_boxed_2915_; size_t v_i_boxed_2916_; lean_object* v_res_2917_; 
v_sz_boxed_2915_ = lean_unbox_usize(v_sz_2905_);
lean_dec(v_sz_2905_);
v_i_boxed_2916_ = lean_unbox_usize(v_i_2906_);
lean_dec(v_i_2906_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_boxed_2915_, v_i_boxed_2916_, v_bs_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2917_;
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
