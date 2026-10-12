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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(lean_object* v_k_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
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
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_8_ = stack[0].m_obj;
lean_object* v___y_9_ = stack[1].m_obj;
lean_object* v___y_10_ = stack[2].m_obj;
lean_object* v_b_11_ = stack[3].m_obj;
lean_object* v_c_12_ = stack[4].m_obj;
lean_object* v___y_13_ = stack[5].m_obj;
lean_object* v___y_14_ = stack[6].m_obj;
lean_object* v___y_15_ = stack[7].m_obj;
lean_object* v___y_16_ = stack[8].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(v_k_8_, v___y_9_, v___y_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed(lean_object* v_k_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v_b_23_, lean_object* v_c_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0(v_k_20_, v___y_21_, v___y_22_, v_b_23_, v_c_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(lean_object* v_type_31_, lean_object* v_k_32_, uint8_t v_cleanupAnnotations_33_, uint8_t v_whnfType_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; 
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_42_, 0, v_k_32_);
lean_closure_set(v___f_42_, 1, v___y_35_);
lean_closure_set(v___f_42_, 2, v___y_36_);
v___x_43_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_31_, v___f_42_, v_cleanupAnnotations_33_, v_whnfType_34_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_43_) == 0)
{
return v___x_43_;
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_31_ = stack[0].m_obj;
lean_object* v_k_32_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_33_ = stack[2].m_num;
uint8_t v_whnfType_34_ = stack[3].m_num;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v___y_40_ = stack[9].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_31_, v_k_32_, v_cleanupAnnotations_33_, v_whnfType_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___boxed(lean_object* v_type_53_, lean_object* v_k_54_, lean_object* v_cleanupAnnotations_55_, lean_object* v_whnfType_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_64_; uint8_t v_whnfType_boxed_65_; lean_object* v_res_66_; 
v_cleanupAnnotations_boxed_64_ = lean_unbox(v_cleanupAnnotations_55_);
v_whnfType_boxed_65_ = lean_unbox(v_whnfType_56_);
v_res_66_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_53_, v_k_54_, v_cleanupAnnotations_boxed_64_, v_whnfType_boxed_65_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_66_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(lean_object* v_00_u03b1_67_, lean_object* v_type_68_, lean_object* v_k_69_, uint8_t v_cleanupAnnotations_70_, uint8_t v_whnfType_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_68_, v_k_69_, v_cleanupAnnotations_70_, v_whnfType_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_68_ = stack[1].m_obj;
lean_object* v_k_69_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_70_ = stack[3].m_num;
uint8_t v_whnfType_71_ = stack[4].m_num;
lean_object* v___y_72_ = stack[5].m_obj;
lean_object* v___y_73_ = stack[6].m_obj;
lean_object* v___y_74_ = stack[7].m_obj;
lean_object* v___y_75_ = stack[8].m_obj;
lean_object* v___y_76_ = stack[9].m_obj;
lean_object* v___y_77_ = stack[10].m_obj;
lean_object* v_res_80_;
v_res_80_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(lean_box(0), v_type_68_, v_k_69_, v_cleanupAnnotations_70_, v_whnfType_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___boxed(lean_object* v_00_u03b1_81_, lean_object* v_type_82_, lean_object* v_k_83_, lean_object* v_cleanupAnnotations_84_, lean_object* v_whnfType_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_93_; uint8_t v_whnfType_boxed_94_; lean_object* v_res_95_; 
v_cleanupAnnotations_boxed_93_ = lean_unbox(v_cleanupAnnotations_84_);
v_whnfType_boxed_94_ = lean_unbox(v_whnfType_85_);
v_res_95_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1(v_00_u03b1_81_, v_type_82_, v_k_83_, v_cleanupAnnotations_boxed_93_, v_whnfType_boxed_94_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_95_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(lean_object* v_as_96_, size_t v_sz_97_, size_t v_i_98_, lean_object* v_b_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_usize_dec_lt(v_i_98_, v_sz_97_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v_b_99_);
return v___x_105_;
}
else
{
lean_object* v_a_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_a_106_ = lean_array_uget_borrowed(v_as_96_, v_i_98_);
v___x_107_ = l_Lean_Expr_fvarId_x21(v_a_106_);
v___x_108_ = l_Lean_FVarId_getDecl___redArg(v___x_107_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = l_Lean_LocalDecl_userName(v_a_109_);
lean_dec(v_a_109_);
v___x_111_ = l_Lean_Name_eraseMacroScopes(v___x_110_);
lean_dec(v___x_110_);
v___x_112_ = l_Lean_Core_mkFreshUserName(v___x_111_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_114_; size_t v___x_115_; size_t v___x_116_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
v___x_114_ = lean_array_push(v_b_99_, v_a_113_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_add(v_i_98_, v___x_115_);
v_i_98_ = v___x_116_;
v_b_99_ = v___x_114_;
goto _start;
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_b_99_);
v_a_118_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_112_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_112_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
lean_dec_ref(v_b_99_);
v_a_126_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_108_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_108_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_96_ = stack[0].m_obj;
size_t v_sz_97_ = stack[1].m_num;
size_t v_i_98_ = stack[2].m_num;
lean_object* v_b_99_ = stack[3].m_obj;
lean_object* v___y_100_ = stack[4].m_obj;
lean_object* v___y_101_ = stack[5].m_obj;
lean_object* v___y_102_ = stack[6].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_96_, v_sz_97_, v_i_98_, v_b_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg___boxed(lean_object* v_as_135_, lean_object* v_sz_136_, lean_object* v_i_137_, lean_object* v_b_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
size_t v_sz_boxed_143_; size_t v_i_boxed_144_; lean_object* v_res_145_; 
v_sz_boxed_143_ = lean_unbox_usize(v_sz_136_);
lean_dec(v_sz_136_);
v_i_boxed_144_ = lean_unbox_usize(v_i_137_);
lean_dec(v_i_137_);
v_res_145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_135_, v_sz_boxed_143_, v_i_boxed_144_, v_b_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec_ref(v_as_135_);
return v_res_145_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0(lean_object* v_xs_148_, lean_object* v_x_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_argNames_157_; size_t v_sz_158_; size_t v___x_159_; lean_object* v___x_160_; 
v_argNames_157_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v_sz_158_ = lean_array_size(v_xs_148_);
v___x_159_ = ((size_t)0ULL);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_xs_148_, v_sz_158_, v___x_159_, v_argNames_157_, v___y_152_, v___y_154_, v___y_155_);
return v___x_160_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInductArgNames___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_148_ = stack[0].m_obj;
lean_object* v_x_149_ = stack[1].m_obj;
lean_object* v___y_150_ = stack[2].m_obj;
lean_object* v___y_151_ = stack[3].m_obj;
lean_object* v___y_152_ = stack[4].m_obj;
lean_object* v___y_153_ = stack[5].m_obj;
lean_object* v___y_154_ = stack[6].m_obj;
lean_object* v___y_155_ = stack[7].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0(v_xs_148_, v_x_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___lam__0___boxed(lean_object* v_xs_162_, lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Elab_Deriving_mkInductArgNames___lam__0(v_xs_162_, v_x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec_ref(v_x_163_);
lean_dec_ref(v_xs_162_);
return v_res_171_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object* v_indVal_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_toConstantVal_181_; lean_object* v_type_182_; lean_object* v___f_183_; uint8_t v___x_184_; lean_object* v___x_185_; 
v_toConstantVal_181_ = lean_ctor_get(v_indVal_173_, 0);
lean_inc_ref(v_toConstantVal_181_);
lean_dec_ref(v_indVal_173_);
v_type_182_ = lean_ctor_get(v_toConstantVal_181_, 2);
lean_inc_ref(v_type_182_);
lean_dec_ref(v_toConstantVal_181_);
v___f_183_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___closed__0));
v___x_184_ = 0;
v___x_185_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg(v_type_182_, v___f_183_, v___x_184_, v___x_184_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInductArgNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_173_ = stack[0].m_obj;
lean_object* v_a_174_ = stack[1].m_obj;
lean_object* v_a_175_ = stack[2].m_obj;
lean_object* v_a_176_ = stack[3].m_obj;
lean_object* v_a_177_ = stack[4].m_obj;
lean_object* v_a_178_ = stack[5].m_obj;
lean_object* v_a_179_ = stack[6].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductArgNames___boxed(lean_object* v_indVal_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_195_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(lean_object* v_as_196_, size_t v_sz_197_, size_t v_i_198_, lean_object* v_b_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___redArg(v_as_196_, v_sz_197_, v_i_198_, v_b_199_, v___y_202_, v___y_204_, v___y_205_);
return v___x_207_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_196_ = stack[0].m_obj;
size_t v_sz_197_ = stack[1].m_num;
size_t v_i_198_ = stack[2].m_num;
lean_object* v_b_199_ = stack[3].m_obj;
lean_object* v___y_200_ = stack[4].m_obj;
lean_object* v___y_201_ = stack[5].m_obj;
lean_object* v___y_202_ = stack[6].m_obj;
lean_object* v___y_203_ = stack[7].m_obj;
lean_object* v___y_204_ = stack[8].m_obj;
lean_object* v___y_205_ = stack[9].m_obj;
lean_object* v_res_208_;
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(v_as_196_, v_sz_197_, v_i_198_, v_b_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0___boxed(lean_object* v_as_209_, lean_object* v_sz_210_, lean_object* v_i_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
size_t v_sz_boxed_220_; size_t v_i_boxed_221_; lean_object* v_res_222_; 
v_sz_boxed_220_ = lean_unbox_usize(v_sz_210_);
lean_dec(v_sz_210_);
v_i_boxed_221_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_res_222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_mkInductArgNames_spec__0(v_as_209_, v_sz_boxed_220_, v_i_boxed_221_, v_b_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_as_209_);
return v_res_222_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(size_t v_sz_223_, size_t v_i_224_, lean_object* v_bs_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_usize_dec_lt(v_i_224_, v_sz_223_);
if (v___x_226_ == 0)
{
return v_bs_225_;
}
else
{
lean_object* v_v_227_; lean_object* v___x_228_; lean_object* v_bs_x27_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v_v_227_ = lean_array_uget(v_bs_225_, v_i_224_);
v___x_228_ = lean_unsigned_to_nat(0u);
v_bs_x27_229_ = lean_array_uset(v_bs_225_, v_i_224_, v___x_228_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_224_, v___x_230_);
v___x_232_ = lean_array_uset(v_bs_x27_229_, v_i_224_, v_v_227_);
v_i_224_ = v___x_231_;
v_bs_225_ = v___x_232_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_223_ = stack[0].m_num;
size_t v_i_224_ = stack[1].m_num;
lean_object* v_bs_225_ = stack[2].m_obj;
lean_object* v_res_234_;
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_223_, v_i_224_, v_bs_225_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1___boxed(lean_object* v_sz_235_, lean_object* v_i_236_, lean_object* v_bs_237_){
_start:
{
size_t v_sz_boxed_238_; size_t v_i_boxed_239_; lean_object* v_res_240_; 
v_sz_boxed_238_ = lean_unbox_usize(v_sz_235_);
lean_dec(v_sz_235_);
v_i_boxed_239_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_boxed_238_, v_i_boxed_239_, v_bs_237_);
return v_res_240_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(size_t v_sz_241_, size_t v_i_242_, lean_object* v_bs_243_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = lean_usize_dec_lt(v_i_242_, v_sz_241_);
if (v___x_244_ == 0)
{
return v_bs_243_;
}
else
{
lean_object* v_v_245_; lean_object* v___x_246_; lean_object* v_bs_x27_247_; lean_object* v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; 
v_v_245_ = lean_array_uget(v_bs_243_, v_i_242_);
v___x_246_ = lean_unsigned_to_nat(0u);
v_bs_x27_247_ = lean_array_uset(v_bs_243_, v_i_242_, v___x_246_);
v___x_248_ = l_Lean_mkIdent(v_v_245_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_add(v_i_242_, v___x_249_);
v___x_251_ = lean_array_uset(v_bs_x27_247_, v_i_242_, v___x_248_);
v_i_242_ = v___x_250_;
v_bs_243_ = v___x_251_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_241_ = stack[0].m_num;
size_t v_i_242_ = stack[1].m_num;
lean_object* v_bs_243_ = stack[2].m_obj;
lean_object* v_res_253_;
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_241_, v_i_242_, v_bs_243_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0___boxed(lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_bs_256_){
_start:
{
size_t v_sz_boxed_257_; size_t v_i_boxed_258_; lean_object* v_res_259_; 
v_sz_boxed_257_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_258_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_boxed_257_, v_i_boxed_258_, v_bs_256_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Array_mkArray0___redArg();
return v___x_279_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object* v_indVal_280_, lean_object* v_argNames_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_toConstantVal_284_; lean_object* v_name_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_311_; 
v_toConstantVal_284_ = lean_ctor_get(v_indVal_280_, 0);
lean_inc_ref(v_toConstantVal_284_);
lean_dec_ref(v_indVal_280_);
v_name_285_ = lean_ctor_get(v_toConstantVal_284_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_toConstantVal_284_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_toConstantVal_284_, 2);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_toConstantVal_284_, 1);
lean_dec(v_unused_313_);
v___x_287_ = v_toConstantVal_284_;
v_isShared_288_ = v_isSharedCheck_311_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_name_285_);
lean_dec(v_toConstantVal_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_311_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_ref_289_; size_t v_sz_290_; lean_object* v_f_291_; size_t v___x_292_; lean_object* v_args_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; size_t v_sz_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v_ref_289_ = lean_ctor_get(v_a_282_, 2);
v_sz_290_ = lean_array_size(v_argNames_281_);
v_f_291_ = l_Lean_mkCIdent(v_name_285_);
v___x_292_ = ((size_t)0ULL);
v_args_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__0(v_sz_290_, v___x_292_, v_argNames_281_);
v___x_294_ = 0;
v___x_295_ = l_Lean_SourceInfo_fromRef(v_ref_289_, v___x_294_);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
v___x_297_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__6));
v___x_298_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__7));
lean_inc_n(v___x_295_, 3);
v___x_299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_295_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = l_Lean_Syntax_node2(v___x_295_, v___x_297_, v___x_299_, v_f_291_);
v___x_301_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_302_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v_sz_303_ = lean_array_size(v_args_293_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInductiveApp_spec__1(v_sz_303_, v___x_292_, v_args_293_);
v___x_305_ = l_Array_append___redArg(v___x_302_, v___x_304_);
lean_dec_ref(v___x_304_);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 1);
lean_ctor_set(v___x_287_, 2, v___x_305_);
lean_ctor_set(v___x_287_, 1, v___x_301_);
lean_ctor_set(v___x_287_, 0, v___x_295_);
v___x_307_ = v___x_287_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_305_);
v___x_307_ = v_reuseFailAlloc_310_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Lean_Syntax_node2(v___x_295_, v___x_296_, v___x_300_, v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInductiveApp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_280_ = stack[0].m_obj;
lean_object* v_argNames_281_ = stack[1].m_obj;
lean_object* v_a_282_ = stack[2].m_obj;
lean_object* v_res_314_;
v_res_314_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_280_, v_argNames_281_, v_a_282_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg___boxed(lean_object* v_indVal_315_, lean_object* v_argNames_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_315_, v_argNames_316_, v_a_317_);
lean_dec_ref(v_a_317_);
return v_res_319_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInductiveApp(lean_object* v_indVal_320_, lean_object* v_argNames_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_320_, v_argNames_321_, v_a_326_);
return v___x_329_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInductiveApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_320_ = stack[0].m_obj;
lean_object* v_argNames_321_ = stack[1].m_obj;
lean_object* v_a_322_ = stack[2].m_obj;
lean_object* v_a_323_ = stack[3].m_obj;
lean_object* v_a_324_ = stack[4].m_obj;
lean_object* v_a_325_ = stack[5].m_obj;
lean_object* v_a_326_ = stack[6].m_obj;
lean_object* v_a_327_ = stack[7].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_Elab_Deriving_mkInductiveApp(v_indVal_320_, v_argNames_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInductiveApp___boxed(lean_object* v_indVal_331_, lean_object* v_argNames_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_Deriving_mkInductiveApp(v_indVal_331_, v_argNames_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_340_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(size_t v_sz_349_, size_t v_i_350_, lean_object* v_bs_351_, lean_object* v___y_352_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_usize_dec_lt(v_i_350_, v_sz_349_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_bs_351_);
return v___x_355_;
}
else
{
lean_object* v_ref_356_; lean_object* v_v_357_; lean_object* v___x_358_; lean_object* v_bs_x27_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v_ref_356_ = lean_ctor_get(v___y_352_, 2);
v_v_357_ = lean_array_uget(v_bs_351_, v_i_350_);
v___x_358_ = lean_unsigned_to_nat(0u);
v_bs_x27_359_ = lean_array_uset(v_bs_351_, v_i_350_, v___x_358_);
v___x_360_ = 0;
v___x_361_ = l_Lean_SourceInfo_fromRef(v_ref_356_, v___x_360_);
v___x_362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__1));
v___x_363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__2));
lean_inc_n(v___x_361_, 4);
v___x_364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_361_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_366_ = l_Lean_mkIdent(v_v_357_);
v___x_367_ = l_Lean_Syntax_node1(v___x_361_, v___x_365_, v___x_366_);
v___x_368_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_361_);
lean_ctor_set(v___x_369_, 1, v___x_365_);
lean_ctor_set(v___x_369_, 2, v___x_368_);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___closed__3));
v___x_371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_361_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = l_Lean_Syntax_node4(v___x_361_, v___x_362_, v___x_364_, v___x_367_, v___x_369_, v___x_371_);
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_350_, v___x_373_);
v___x_375_ = lean_array_uset(v_bs_x27_359_, v_i_350_, v___x_372_);
v_i_350_ = v___x_374_;
v_bs_351_ = v___x_375_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_349_ = stack[0].m_num;
size_t v_i_350_ = stack[1].m_num;
lean_object* v_bs_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v_res_377_;
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_349_, v_i_350_, v_bs_351_, v___y_352_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg___boxed(lean_object* v_sz_378_, lean_object* v_i_379_, lean_object* v_bs_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_378_);
lean_dec(v_sz_378_);
v_i_boxed_384_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_boxed_383_, v_i_boxed_384_, v_bs_380_, v___y_381_);
lean_dec_ref(v___y_381_);
return v_res_385_;
}
}
lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object* v_argNames_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
size_t v_sz_394_; size_t v___x_395_; lean_object* v___x_396_; 
v_sz_394_ = lean_array_size(v_argNames_386_);
v___x_395_ = ((size_t)0ULL);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_394_, v___x_395_, v_argNames_386_, v_a_391_);
return v___x_396_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkImplicitBinders_0interp(lean_interpreter_value* stack)
{
lean_object* v_argNames_386_ = stack[0].m_obj;
lean_object* v_a_387_ = stack[1].m_obj;
lean_object* v_a_388_ = stack[2].m_obj;
lean_object* v_a_389_ = stack[3].m_obj;
lean_object* v_a_390_ = stack[4].m_obj;
lean_object* v_a_391_ = stack[5].m_obj;
lean_object* v_a_392_ = stack[6].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_argNames_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkImplicitBinders___boxed(lean_object* v_argNames_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_argNames_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_406_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(size_t v_sz_407_, size_t v_i_408_, lean_object* v_bs_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___redArg(v_sz_407_, v_i_408_, v_bs_409_, v___y_414_);
return v___x_417_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_407_ = stack[0].m_num;
size_t v_i_408_ = stack[1].m_num;
lean_object* v_bs_409_ = stack[2].m_obj;
lean_object* v___y_410_ = stack[3].m_obj;
lean_object* v___y_411_ = stack[4].m_obj;
lean_object* v___y_412_ = stack[5].m_obj;
lean_object* v___y_413_ = stack[6].m_obj;
lean_object* v___y_414_ = stack[7].m_obj;
lean_object* v___y_415_ = stack[8].m_obj;
lean_object* v_res_418_;
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(v_sz_407_, v_i_408_, v_bs_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0___boxed(lean_object* v_sz_419_, lean_object* v_i_420_, lean_object* v_bs_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
size_t v_sz_boxed_429_; size_t v_i_boxed_430_; lean_object* v_res_431_; 
v_sz_boxed_429_ = lean_unbox_usize(v_sz_419_);
lean_dec(v_sz_419_);
v_i_boxed_430_ = lean_unbox_usize(v_i_420_);
lean_dec(v_i_420_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkImplicitBinders_spec__0(v_sz_boxed_429_, v_i_boxed_430_, v_bs_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_431_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(lean_object* v_type_432_, lean_object* v_maxFVars_x3f_433_, lean_object* v_k_434_, uint8_t v_cleanupAnnotations_435_, uint8_t v_whnfType_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; 
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
v___f_444_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_mkInductArgNames_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_444_, 0, v_k_434_);
lean_closure_set(v___f_444_, 1, v___y_437_);
lean_closure_set(v___f_444_, 2, v___y_438_);
v___x_445_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_432_, v_maxFVars_x3f_433_, v___f_444_, v_cleanupAnnotations_435_, v_whnfType_436_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_445_) == 0)
{
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_432_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_433_ = stack[1].m_obj;
lean_object* v_k_434_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_435_ = stack[3].m_num;
uint8_t v_whnfType_436_ = stack[4].m_num;
lean_object* v___y_437_ = stack[5].m_obj;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v___y_439_ = stack[7].m_obj;
lean_object* v___y_440_ = stack[8].m_obj;
lean_object* v___y_441_ = stack[9].m_obj;
lean_object* v___y_442_ = stack[10].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_432_, v_maxFVars_x3f_433_, v_k_434_, v_cleanupAnnotations_435_, v_whnfType_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg___boxed(lean_object* v_type_455_, lean_object* v_maxFVars_x3f_456_, lean_object* v_k_457_, lean_object* v_cleanupAnnotations_458_, lean_object* v_whnfType_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_467_; uint8_t v_whnfType_boxed_468_; lean_object* v_res_469_; 
v_cleanupAnnotations_boxed_467_ = lean_unbox(v_cleanupAnnotations_458_);
v_whnfType_boxed_468_ = lean_unbox(v_whnfType_459_);
v_res_469_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_455_, v_maxFVars_x3f_456_, v_k_457_, v_cleanupAnnotations_boxed_467_, v_whnfType_boxed_468_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_469_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(lean_object* v_00_u03b1_470_, lean_object* v_type_471_, lean_object* v_maxFVars_x3f_472_, lean_object* v_k_473_, uint8_t v_cleanupAnnotations_474_, uint8_t v_whnfType_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_471_, v_maxFVars_x3f_472_, v_k_473_, v_cleanupAnnotations_474_, v_whnfType_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_483_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_471_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_472_ = stack[2].m_obj;
lean_object* v_k_473_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_474_ = stack[4].m_num;
uint8_t v_whnfType_475_ = stack[5].m_num;
lean_object* v___y_476_ = stack[6].m_obj;
lean_object* v___y_477_ = stack[7].m_obj;
lean_object* v___y_478_ = stack[8].m_obj;
lean_object* v___y_479_ = stack[9].m_obj;
lean_object* v___y_480_ = stack[10].m_obj;
lean_object* v___y_481_ = stack[11].m_obj;
lean_object* v_res_484_;
v_res_484_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(lean_box(0), v_type_471_, v_maxFVars_x3f_472_, v_k_473_, v_cleanupAnnotations_474_, v_whnfType_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
stack->m_obj
 = v_res_484_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___boxed(lean_object* v_00_u03b1_485_, lean_object* v_type_486_, lean_object* v_maxFVars_x3f_487_, lean_object* v_k_488_, lean_object* v_cleanupAnnotations_489_, lean_object* v_whnfType_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_498_; uint8_t v_whnfType_boxed_499_; lean_object* v_res_500_; 
v_cleanupAnnotations_boxed_498_ = lean_unbox(v_cleanupAnnotations_489_);
v_whnfType_boxed_499_ = lean_unbox(v_whnfType_490_);
v_res_500_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1(v_00_u03b1_485_, v_type_486_, v_maxFVars_x3f_487_, v_k_488_, v_cleanupAnnotations_boxed_498_, v_whnfType_boxed_499_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_500_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(lean_object* v_upperBound_509_, lean_object* v_xs_510_, lean_object* v_className_511_, lean_object* v_argNames_512_, lean_object* v_a_513_, lean_object* v_b_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_snd_521_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v_a_530_; uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_lt(v_a_513_, v_upperBound_509_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_dec(v_a_513_);
lean_dec(v_className_511_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v_b_514_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_array_fget_borrowed(v_xs_510_, v_a_513_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_mk_empty_array_with_capacity(v___x_537_);
lean_inc(v___x_536_);
v___x_539_ = lean_array_push(v___x_538_, v___x_536_);
lean_inc(v_className_511_);
v___x_540_ = l_Lean_Meta_mkAppM(v_className_511_, v___x_539_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = l_Lean_Meta_isTypeCorrect(v_a_541_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; uint8_t v___x_544_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_unbox(v_a_543_);
lean_dec(v_a_543_);
if (v___x_544_ == 0)
{
v_snd_521_ = v_b_514_;
goto v___jp_520_;
}
else
{
lean_object* v_ref_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_ref_545_ = lean_ctor_get(v___y_517_, 2);
v___x_546_ = lean_array_get_borrowed(v___x_535_, v_argNames_512_, v_a_513_);
v___x_547_ = 0;
v___x_548_ = l_Lean_SourceInfo_fromRef(v_ref_545_, v___x_547_);
v___x_549_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__1));
v___x_550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__2));
lean_inc_n(v___x_548_, 5);
v___x_551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_548_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_553_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_548_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_511_);
v___x_556_ = l_Lean_mkCIdent(v_className_511_);
lean_inc(v___x_546_);
v___x_557_ = l_Lean_mkIdent(v___x_546_);
v___x_558_ = l_Lean_Syntax_node1(v___x_548_, v___x_552_, v___x_557_);
v___x_559_ = l_Lean_Syntax_node2(v___x_548_, v___x_555_, v___x_556_, v___x_558_);
v___x_560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___closed__3));
v___x_561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_548_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_Syntax_node4(v___x_548_, v___x_549_, v___x_551_, v___x_554_, v___x_559_, v___x_561_);
v___x_563_ = lean_array_push(v_b_514_, v___x_562_);
v_snd_521_ = v___x_563_;
goto v___jp_520_;
}
}
else
{
lean_object* v_a_564_; 
v_a_564_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_542_, 1);
v_a_530_ = v_a_564_;
goto v___jp_529_;
}
}
else
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_540_, 1);
v_a_530_ = v_a_565_;
goto v___jp_529_;
}
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_a_513_, v___x_522_);
lean_dec(v_a_513_);
v_a_513_ = v___x_523_;
v_b_514_ = v_snd_521_;
goto _start;
}
v___jp_525_:
{
if (v___y_527_ == 0)
{
lean_dec_ref(v___y_526_);
v_snd_521_ = v_b_514_;
goto v___jp_520_;
}
else
{
lean_object* v___x_528_; 
lean_dec_ref(v_b_514_);
lean_dec(v_a_513_);
lean_dec(v_className_511_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___y_526_);
return v___x_528_;
}
}
v___jp_529_:
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_Exception_isInterrupt(v_a_530_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
lean_inc_ref(v_a_530_);
v___x_532_ = l_Lean_Exception_isRuntime(v_a_530_);
v___y_526_ = v_a_530_;
v___y_527_ = v___x_532_;
goto v___jp_525_;
}
else
{
v___y_526_ = v_a_530_;
v___y_527_ = v___x_531_;
goto v___jp_525_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_509_ = stack[0].m_obj;
lean_object* v_xs_510_ = stack[1].m_obj;
lean_object* v_className_511_ = stack[2].m_obj;
lean_object* v_argNames_512_ = stack[3].m_obj;
lean_object* v_a_513_ = stack[4].m_obj;
lean_object* v_b_514_ = stack[5].m_obj;
lean_object* v___y_515_ = stack[6].m_obj;
lean_object* v___y_516_ = stack[7].m_obj;
lean_object* v___y_517_ = stack[8].m_obj;
lean_object* v___y_518_ = stack[9].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_509_, v_xs_510_, v_className_511_, v_argNames_512_, v_a_513_, v_b_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg___boxed(lean_object* v_upperBound_567_, lean_object* v_xs_568_, lean_object* v_className_569_, lean_object* v_argNames_570_, lean_object* v_a_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_567_, v_xs_568_, v_className_569_, v_argNames_570_, v_a_571_, v_b_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_argNames_570_);
lean_dec_ref(v_xs_568_);
lean_dec(v_upperBound_567_);
return v_res_578_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(lean_object* v_className_581_, lean_object* v_argNames_582_, lean_object* v_xs_583_, lean_object* v_x_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_binders_594_; lean_object* v___x_595_; 
v___x_592_ = lean_array_get_size(v_xs_583_);
v___x_593_ = lean_unsigned_to_nat(0u);
v_binders_594_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v___x_592_, v_xs_583_, v_className_581_, v_argNames_582_, v___x_593_, v_binders_594_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_595_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_className_581_ = stack[0].m_obj;
lean_object* v_argNames_582_ = stack[1].m_obj;
lean_object* v_xs_583_ = stack[2].m_obj;
lean_object* v_x_584_ = stack[3].m_obj;
lean_object* v___y_585_ = stack[4].m_obj;
lean_object* v___y_586_ = stack[5].m_obj;
lean_object* v___y_587_ = stack[6].m_obj;
lean_object* v___y_588_ = stack[7].m_obj;
lean_object* v___y_589_ = stack[8].m_obj;
lean_object* v___y_590_ = stack[9].m_obj;
lean_object* v_res_596_;
v_res_596_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(v_className_581_, v_argNames_582_, v_xs_583_, v_x_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed(lean_object* v_className_597_, lean_object* v_argNames_598_, lean_object* v_xs_599_, lean_object* v_x_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0(v_className_597_, v_argNames_598_, v_xs_599_, v_x_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_xs_599_);
lean_dec_ref(v_argNames_598_);
return v_res_608_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object* v_className_609_, lean_object* v_indVal_610_, lean_object* v_argNames_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_toConstantVal_619_; lean_object* v_numParams_620_; lean_object* v_type_621_; lean_object* v___f_622_; lean_object* v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; 
v_toConstantVal_619_ = lean_ctor_get(v_indVal_610_, 0);
lean_inc_ref(v_toConstantVal_619_);
v_numParams_620_ = lean_ctor_get(v_indVal_610_, 1);
lean_inc(v_numParams_620_);
lean_dec_ref(v_indVal_610_);
v_type_621_ = lean_ctor_get(v_toConstantVal_619_, 2);
lean_inc_ref(v_type_621_);
lean_dec_ref(v_toConstantVal_619_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___boxed), 11, 2);
lean_closure_set(v___f_622_, 0, v_className_609_);
lean_closure_set(v___f_622_, 1, v_argNames_611_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v_numParams_620_);
v___x_624_ = 0;
v___x_625_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__1___redArg(v_type_621_, v___x_623_, v___f_622_, v___x_624_, v___x_624_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
return v___x_625_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInstImplicitBinders_0interp(lean_interpreter_value* stack)
{
lean_object* v_className_609_ = stack[0].m_obj;
lean_object* v_indVal_610_ = stack[1].m_obj;
lean_object* v_argNames_611_ = stack[2].m_obj;
lean_object* v_a_612_ = stack[3].m_obj;
lean_object* v_a_613_ = stack[4].m_obj;
lean_object* v_a_614_ = stack[5].m_obj;
lean_object* v_a_615_ = stack[6].m_obj;
lean_object* v_a_616_ = stack[7].m_obj;
lean_object* v_a_617_ = stack[8].m_obj;
lean_object* v_res_626_;
v_res_626_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_609_, v_indVal_610_, v_argNames_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
stack->m_obj
 = v_res_626_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders___boxed(lean_object* v_className_627_, lean_object* v_indVal_628_, lean_object* v_argNames_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_627_, v_indVal_628_, v_argNames_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_637_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(lean_object* v_upperBound_638_, lean_object* v_xs_639_, lean_object* v_className_640_, lean_object* v_argNames_641_, lean_object* v_inst_642_, lean_object* v_R_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v_c_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___redArg(v_upperBound_638_, v_xs_639_, v_className_640_, v_argNames_641_, v_a_644_, v_b_645_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
return v___x_654_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_638_ = stack[0].m_obj;
lean_object* v_xs_639_ = stack[1].m_obj;
lean_object* v_className_640_ = stack[2].m_obj;
lean_object* v_argNames_641_ = stack[3].m_obj;
lean_object* v_a_644_ = stack[6].m_obj;
lean_object* v_b_645_ = stack[7].m_obj;
lean_object* v___y_647_ = stack[9].m_obj;
lean_object* v___y_648_ = stack[10].m_obj;
lean_object* v___y_649_ = stack[11].m_obj;
lean_object* v___y_650_ = stack[12].m_obj;
lean_object* v___y_651_ = stack[13].m_obj;
lean_object* v___y_652_ = stack[14].m_obj;
lean_object* v_res_655_;
v_res_655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(v_upperBound_638_, v_xs_639_, v_className_640_, v_argNames_641_, lean_box(0), lean_box(0), v_a_644_, v_b_645_, lean_box(0), v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0___boxed(lean_object* v_upperBound_656_, lean_object* v_xs_657_, lean_object* v_className_658_, lean_object* v_argNames_659_, lean_object* v_inst_660_, lean_object* v_R_661_, lean_object* v_a_662_, lean_object* v_b_663_, lean_object* v_c_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstImplicitBinders_spec__0(v_upperBound_656_, v_xs_657_, v_className_658_, v_argNames_659_, v_inst_660_, v_R_661_, v_a_662_, v_b_663_, v_c_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_argNames_659_);
lean_dec_ref(v_xs_657_);
lean_dec(v_upperBound_656_);
return v_res_672_;
}
}
lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(uint8_t v___x_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
if (lean_obj_tag(v_a_696_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = l_List_reverse___redArg(v_a_697_);
return v___x_698_;
}
else
{
lean_object* v_head_699_; lean_object* v_tail_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_730_; 
v_head_699_ = lean_ctor_get(v_a_696_, 0);
v_tail_700_ = lean_ctor_get(v_a_696_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_730_ == 0)
{
v___x_702_ = v_a_696_;
v_isShared_703_ = v_isSharedCheck_730_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_tail_700_);
lean_inc(v_head_699_);
lean_dec(v_a_696_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_730_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___y_705_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1));
lean_inc(v_head_699_);
v___x_713_ = l_Lean_Syntax_isOfKind(v_head_699_, v___x_712_);
if (v___x_713_ == 0)
{
v___y_705_ = v___x_713_;
goto v___jp_704_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l_Lean_Syntax_getArg(v_head_699_, v___x_714_);
v___x_716_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3));
lean_inc(v___x_715_);
v___x_717_ = l_Lean_Syntax_isOfKind(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec(v___x_715_);
v___y_705_ = v___x_717_;
goto v___jp_704_;
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Syntax_getArg(v___x_715_, v___x_714_);
lean_dec(v___x_715_);
v___x_719_ = l_Lean_Syntax_matchesNull(v___x_718_, v___x_714_);
if (v___x_719_ == 0)
{
v___y_705_ = v___x_719_;
goto v___jp_704_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = l_Lean_Syntax_getArg(v_head_699_, v___x_720_);
v___x_722_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6));
lean_inc(v___x_721_);
v___x_723_ = l_Lean_Syntax_isOfKind(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v___x_721_);
v___y_705_ = v___x_723_;
goto v___jp_704_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_724_ = l_Lean_Syntax_getArg(v___x_721_, v___x_714_);
v___x_725_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8));
v___x_726_ = l_Lean_Syntax_matchesIdent(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
if (v___x_726_ == 0)
{
lean_dec(v___x_721_);
v___y_705_ = v___x_726_;
goto v___jp_704_;
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = l_Lean_Syntax_getArg(v___x_721_, v___x_720_);
lean_dec(v___x_721_);
v___x_728_ = l_Lean_Syntax_matchesNull(v___x_727_, v___x_714_);
if (v___x_728_ == 0)
{
v___y_705_ = v___x_728_;
goto v___jp_704_;
}
else
{
lean_del_object(v___x_702_);
lean_dec(v_head_699_);
v_a_696_ = v_tail_700_;
goto _start;
}
}
}
}
}
}
v___jp_704_:
{
if (v___y_705_ == 0)
{
if (v___x_695_ == 0)
{
lean_del_object(v___x_702_);
lean_dec(v_head_699_);
v_a_696_ = v_tail_700_;
goto _start;
}
else
{
lean_object* v___x_708_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_a_697_);
v___x_708_ = v___x_702_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_head_699_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_697_);
v___x_708_ = v_reuseFailAlloc_710_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v_a_696_ = v_tail_700_;
v_a_697_ = v___x_708_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_702_);
lean_dec(v_head_699_);
v_a_696_ = v_tail_700_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_695_ = stack[0].m_num;
lean_object* v_a_696_ = stack[1].m_obj;
lean_object* v_a_697_ = stack[2].m_obj;
lean_object* v_res_731_;
v_res_731_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_695_, v_a_696_, v_a_697_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___boxed(lean_object* v___x_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
uint8_t v___x_3735__boxed_735_; lean_object* v_res_736_; 
v___x_3735__boxed_735_ = lean_unbox(v___x_732_);
v_res_736_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_3735__boxed_735_, v_a_733_, v_a_734_);
return v_res_736_;
}
}
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(uint8_t v___x_737_, lean_object* v_sc_738_){
_start:
{
lean_object* v_header_739_; lean_object* v_opts_740_; lean_object* v_currNamespace_741_; lean_object* v_openDecls_742_; lean_object* v_levelNames_743_; lean_object* v_varDecls_744_; lean_object* v_varUIds_745_; lean_object* v_includedVars_746_; lean_object* v_omittedVars_747_; uint8_t v_isNoncomputable_748_; uint8_t v_isPublic_749_; uint8_t v_isMeta_750_; lean_object* v_attrs_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_760_; 
v_header_739_ = lean_ctor_get(v_sc_738_, 0);
v_opts_740_ = lean_ctor_get(v_sc_738_, 1);
v_currNamespace_741_ = lean_ctor_get(v_sc_738_, 2);
v_openDecls_742_ = lean_ctor_get(v_sc_738_, 3);
v_levelNames_743_ = lean_ctor_get(v_sc_738_, 4);
v_varDecls_744_ = lean_ctor_get(v_sc_738_, 5);
v_varUIds_745_ = lean_ctor_get(v_sc_738_, 6);
v_includedVars_746_ = lean_ctor_get(v_sc_738_, 7);
v_omittedVars_747_ = lean_ctor_get(v_sc_738_, 8);
v_isNoncomputable_748_ = lean_ctor_get_uint8(v_sc_738_, sizeof(void*)*10);
v_isPublic_749_ = lean_ctor_get_uint8(v_sc_738_, sizeof(void*)*10 + 1);
v_isMeta_750_ = lean_ctor_get_uint8(v_sc_738_, sizeof(void*)*10 + 2);
v_attrs_751_ = lean_ctor_get(v_sc_738_, 9);
v_isSharedCheck_760_ = !lean_is_exclusive(v_sc_738_);
if (v_isSharedCheck_760_ == 0)
{
v___x_753_ = v_sc_738_;
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_attrs_751_);
lean_inc(v_omittedVars_747_);
lean_inc(v_includedVars_746_);
lean_inc(v_varUIds_745_);
lean_inc(v_varDecls_744_);
lean_inc(v_levelNames_743_);
lean_inc(v_openDecls_742_);
lean_inc(v_currNamespace_741_);
lean_inc(v_opts_740_);
lean_inc(v_header_739_);
lean_dec(v_sc_738_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_box(0);
v___x_756_ = l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4(v___x_737_, v_attrs_751_, v___x_755_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 9, v___x_756_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_header_739_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_opts_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_currNamespace_741_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_openDecls_742_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_levelNames_743_);
lean_ctor_set(v_reuseFailAlloc_759_, 5, v_varDecls_744_);
lean_ctor_set(v_reuseFailAlloc_759_, 6, v_varUIds_745_);
lean_ctor_set(v_reuseFailAlloc_759_, 7, v_includedVars_746_);
lean_ctor_set(v_reuseFailAlloc_759_, 8, v_omittedVars_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 9, v___x_756_);
lean_ctor_set_uint8(v_reuseFailAlloc_759_, sizeof(void*)*10, v_isNoncomputable_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_759_, sizeof(void*)*10 + 1, v_isPublic_749_);
lean_ctor_set_uint8(v_reuseFailAlloc_759_, sizeof(void*)*10 + 2, v_isMeta_750_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_737_ = stack[0].m_num;
lean_object* v_sc_738_ = stack[1].m_obj;
lean_object* v_res_761_;
v_res_761_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(v___x_737_, v_sc_738_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed(lean_object* v___x_762_, lean_object* v_sc_763_){
_start:
{
uint8_t v___x_3893__boxed_764_; lean_object* v_res_765_; 
v___x_3893__boxed_764_ = lean_unbox(v___x_762_);
v_res_765_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0(v___x_3893__boxed_764_, v_sc_763_);
return v_res_765_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_box(1);
v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__2));
v___x_772_ = l_Lean_MessageData_ofFormat(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
return v_x_773_;
}
else
{
lean_object* v_head_775_; lean_object* v_tail_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_798_; 
v_head_775_ = lean_ctor_get(v_x_774_, 0);
v_tail_776_ = lean_ctor_get(v_x_774_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_798_ == 0)
{
v___x_778_ = v_x_774_;
v_isShared_779_ = v_isSharedCheck_798_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_tail_776_);
lean_inc(v_head_775_);
lean_dec(v_x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_798_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_before_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_796_; 
v_before_780_ = lean_ctor_get(v_head_775_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_head_775_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_head_775_, 1);
lean_dec(v_unused_797_);
v___x_782_ = v_head_775_;
v_isShared_783_ = v_isSharedCheck_796_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_before_780_);
lean_dec(v_head_775_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_796_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 7);
lean_ctor_set(v___x_782_, 1, v___x_784_);
lean_ctor_set(v___x_782_, 0, v_x_773_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_x_773_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_795_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__3);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 7);
lean_ctor_set(v___x_778_, 1, v___x_787_);
lean_ctor_set(v___x_778_, 0, v___x_786_);
v___x_789_ = v___x_778_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_794_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = l_Lean_MessageData_ofSyntax(v_before_780_);
v___x_791_ = l_Lean_indentD(v___x_790_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_789_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v_x_773_ = v___x_792_;
v_x_774_ = v_tail_776_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(lean_object* v_opts_799_, lean_object* v_opt_800_){
_start:
{
lean_object* v_name_801_; lean_object* v_defValue_802_; lean_object* v_map_803_; lean_object* v___x_804_; 
v_name_801_ = lean_ctor_get(v_opt_800_, 0);
v_defValue_802_ = lean_ctor_get(v_opt_800_, 1);
v_map_803_ = lean_ctor_get(v_opts_799_, 0);
v___x_804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_803_, v_name_801_);
if (lean_obj_tag(v___x_804_) == 0)
{
uint8_t v___x_805_; 
v___x_805_ = lean_unbox(v_defValue_802_);
return v___x_805_;
}
else
{
lean_object* v_val_806_; 
v_val_806_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___x_804_, 1);
if (lean_obj_tag(v_val_806_) == 1)
{
uint8_t v_v_807_; 
v_v_807_ = lean_ctor_get_uint8(v_val_806_, 0);
lean_dec_ref_known(v_val_806_, 0);
return v_v_807_;
}
else
{
uint8_t v___x_808_; 
lean_dec(v_val_806_);
v___x_808_ = lean_unbox(v_defValue_802_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_799_ = stack[0].m_obj;
lean_object* v_opt_800_ = stack[1].m_obj;
uint8_t v_res_809_;
v_res_809_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_799_, v_opt_800_);
stack->m_num = v_res_809_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8___boxed(lean_object* v_opts_810_, lean_object* v_opt_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_810_, v_opt_811_);
lean_dec_ref(v_opt_811_);
lean_dec_ref(v_opts_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__1));
v___x_818_ = l_Lean_MessageData_ofFormat(v___x_817_);
return v___x_818_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(lean_object* v_msgData_819_, lean_object* v_macroStack_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_scopes_825_; lean_object* v___x_826_; lean_object* v_opts_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_823_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_824_ = lean_st_ref_get(v___y_821_);
v_scopes_825_ = lean_ctor_get(v___x_824_, 2);
lean_inc(v_scopes_825_);
lean_dec(v___x_824_);
v___x_826_ = l_List_head_x21___redArg(v___x_823_, v_scopes_825_);
lean_dec(v_scopes_825_);
v_opts_827_ = lean_ctor_get(v___x_826_, 1);
lean_inc_ref(v_opts_827_);
lean_dec(v___x_826_);
v___x_828_ = l_Lean_Elab_pp_macroStack;
v___x_829_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v_opts_827_, v___x_828_);
lean_dec_ref(v_opts_827_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v_macroStack_820_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_msgData_819_);
return v___x_830_;
}
else
{
if (lean_obj_tag(v_macroStack_820_) == 0)
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_msgData_819_);
return v___x_831_;
}
else
{
lean_object* v_head_832_; lean_object* v_after_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_848_; 
v_head_832_ = lean_ctor_get(v_macroStack_820_, 0);
lean_inc(v_head_832_);
v_after_833_ = lean_ctor_get(v_head_832_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_head_832_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_head_832_, 0);
lean_dec(v_unused_849_);
v___x_835_ = v_head_832_;
v_isShared_836_ = v_isSharedCheck_848_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_after_833_);
lean_dec(v_head_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_848_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 7);
lean_ctor_set(v___x_835_, 1, v___x_837_);
lean_ctor_set(v___x_835_, 0, v_msgData_819_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_msgData_819_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_847_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_msgData_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_840_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_MessageData_ofSyntax(v_after_833_);
v___x_843_ = l_Lean_indentD(v___x_842_);
v_msgData_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_844_, 0, v___x_841_);
lean_ctor_set(v_msgData_844_, 1, v___x_843_);
v___x_845_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_844_, v_macroStack_820_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_819_ = stack[0].m_obj;
lean_object* v_macroStack_820_ = stack[1].m_obj;
lean_object* v___y_821_ = stack[2].m_obj;
lean_object* v_res_850_;
v_res_850_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_819_, v_macroStack_820_, v___y_821_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___boxed(lean_object* v_msgData_851_, lean_object* v_macroStack_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_851_, v_macroStack_852_, v___y_853_);
lean_dec(v___y_853_);
return v_res_855_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_856_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__0);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_859_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_860_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
lean_ctor_set(v___x_862_, 3, v___x_861_);
lean_ctor_set(v___x_862_, 4, v___x_860_);
lean_ctor_set(v___x_862_, 5, v___x_860_);
lean_ctor_set(v___x_862_, 6, v___x_860_);
lean_ctor_set(v___x_862_, 7, v___x_860_);
lean_ctor_set(v___x_862_, 8, v___x_860_);
lean_ctor_set(v___x_862_, 9, v___x_860_);
lean_ctor_set(v___x_862_, 10, v___x_860_);
lean_ctor_set(v___x_862_, 11, v___x_859_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_unsigned_to_nat(32u);
v___x_864_ = lean_mk_empty_array_with_capacity(v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_866_ = ((size_t)5ULL);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_unsigned_to_nat(32u);
v___x_869_ = lean_mk_empty_array_with_capacity(v___x_868_);
v___x_870_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__3);
v___x_871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
lean_ctor_set(v___x_871_, 2, v___x_867_);
lean_ctor_set(v___x_871_, 3, v___x_867_);
lean_ctor_set_usize(v___x_871_, 4, v___x_866_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = lean_box(1);
v___x_873_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__4);
v___x_874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__1);
v___x_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_873_);
lean_ctor_set(v___x_875_, 2, v___x_872_);
return v___x_875_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(lean_object* v_msgData_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_env_880_; uint8_t v___x_881_; lean_object* v_env_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_scopes_885_; lean_object* v___x_886_; lean_object* v_opts_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_879_ = lean_st_ref_get(v___y_877_);
v_env_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc_ref(v_env_880_);
lean_dec(v___x_879_);
v___x_881_ = 0;
v_env_882_ = l_Lean_Environment_setRecordingDeps(v_env_880_, v___x_881_);
v___x_883_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_884_ = lean_st_ref_get(v___y_877_);
v_scopes_885_ = lean_ctor_get(v___x_884_, 2);
lean_inc(v_scopes_885_);
lean_dec(v___x_884_);
v___x_886_ = l_List_head_x21___redArg(v___x_883_, v_scopes_885_);
lean_dec(v_scopes_885_);
v_opts_887_ = lean_ctor_get(v___x_886_, 1);
lean_inc_ref(v_opts_887_);
lean_dec(v___x_886_);
v___x_888_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__2);
v___x_889_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___closed__5);
v___x_890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_890_, 0, v_env_882_);
lean_ctor_set(v___x_890_, 1, v___x_888_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
lean_ctor_set(v___x_890_, 3, v_opts_887_);
v___x_891_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_msgData_876_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_876_ = stack[0].m_obj;
lean_object* v___y_877_ = stack[1].m_obj;
lean_object* v_res_893_;
v_res_893_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_876_, v___y_877_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg___boxed(lean_object* v_msgData_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_894_, v___y_895_);
lean_dec(v___y_895_);
return v_res_897_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Elab_Command_getRef___redArg(v___y_899_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_macroStack_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_macroStack_904_ = lean_ctor_get(v___y_899_, 4);
v___x_905_ = l_Lean_Elab_getBetterRef(v_a_903_, v_macroStack_904_);
lean_dec(v_a_903_);
v___x_906_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msg_898_, v___y_900_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_906_);
lean_inc(v_macroStack_904_);
v___x_908_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_a_907_, v_macroStack_904_, v___y_900_);
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_917_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_905_);
lean_ctor_set(v___x_913_, 1, v_a_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 1);
lean_ctor_set(v___x_911_, 0, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v_msg_898_);
v_a_918_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_902_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_902_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_898_ = stack[0].m_obj;
lean_object* v___y_899_ = stack[1].m_obj;
lean_object* v___y_900_ = stack[2].m_obj;
lean_object* v_res_926_;
v_res_926_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_898_, v___y_899_, v___y_900_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg___boxed(lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_931_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__2));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(lean_object* v_constName_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v_env_943_; lean_object* v___x_944_; 
v___x_942_ = lean_st_ref_get(v___y_940_);
v_env_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_env_943_);
lean_dec(v___x_942_);
lean_inc(v_constName_938_);
v___x_944_ = l_Lean_isInductiveCore_x3f(v_env_943_, v_constName_938_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_945_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_946_ = 0;
v___x_947_ = l_Lean_MessageData_ofConstName(v_constName_938_, v___x_946_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_945_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_950_, v___y_939_, v___y_940_);
return v___x_951_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_constName_938_);
v_val_952_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_944_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_944_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 0);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_val_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_938_ = stack[0].m_obj;
lean_object* v___y_939_ = stack[1].m_obj;
lean_object* v___y_940_ = stack[2].m_obj;
lean_object* v_res_960_;
v_res_960_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_constName_938_, v___y_939_, v___y_940_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___boxed(lean_object* v_constName_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_constName_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_965_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(lean_object* v_as_x27_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
if (lean_obj_tag(v_as_x27_966_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_b_967_);
return v___x_971_;
}
else
{
lean_object* v_head_972_; lean_object* v_tail_973_; lean_object* v___x_974_; 
v_head_972_ = lean_ctor_get(v_as_x27_966_, 0);
v_tail_973_ = lean_ctor_get(v_as_x27_966_, 1);
lean_inc(v_head_972_);
v___x_974_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_head_972_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = lean_array_push(v_b_967_, v_a_975_);
v_as_x27_966_ = v_tail_973_;
v_b_967_ = v___x_976_;
goto _start;
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_b_967_);
v_a_978_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_974_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_966_ = stack[0].m_obj;
lean_object* v_b_967_ = stack[1].m_obj;
lean_object* v___y_968_ = stack[2].m_obj;
lean_object* v___y_969_ = stack[3].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_966_, v_b_967_, v___y_968_, v___y_969_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg___boxed(lean_object* v_as_x27_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_987_, v_b_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v_as_x27_987_);
return v_res_992_;
}
}
uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(lean_object* v___y_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
uint8_t v___x_995_; 
v___x_995_ = 0;
return v___x_995_;
}
else
{
lean_object* v_head_996_; lean_object* v_tail_997_; uint8_t v___y_999_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v_head_996_ = lean_ctor_get(v_x_994_, 0);
lean_inc_n(v_head_996_, 2);
v_tail_997_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_tail_997_);
lean_dec_ref_known(v_x_994_, 2);
v___x_1001_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__1));
v___x_1002_ = l_Lean_Syntax_isOfKind(v_head_996_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec(v_head_996_);
v___y_999_ = v___x_1002_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = l_Lean_Syntax_getArg(v_head_996_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__3));
lean_inc(v___x_1004_);
v___x_1006_ = l_Lean_Syntax_isOfKind(v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_dec(v___x_1004_);
lean_dec(v_head_996_);
v___y_999_ = v___x_1006_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = l_Lean_Syntax_getArg(v___x_1004_, v___x_1003_);
lean_dec(v___x_1004_);
v___x_1008_ = l_Lean_Syntax_matchesNull(v___x_1007_, v___x_1003_);
if (v___x_1008_ == 0)
{
lean_dec(v_head_996_);
v___y_999_ = v___x_1008_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = l_Lean_Syntax_getArg(v_head_996_, v___x_1009_);
lean_dec(v_head_996_);
v___x_1011_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__6));
lean_inc(v___x_1010_);
v___x_1012_ = l_Lean_Syntax_isOfKind(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_dec(v___x_1010_);
v___y_999_ = v___x_1012_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = l_Lean_Syntax_getArg(v___x_1010_, v___x_1003_);
v___x_1014_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__8));
v___x_1015_ = l_Lean_Syntax_matchesIdent(v___x_1013_, v___x_1014_);
lean_dec(v___x_1013_);
if (v___x_1015_ == 0)
{
lean_dec(v___x_1010_);
v___y_999_ = v___x_1015_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = l_Lean_Syntax_getArg(v___x_1010_, v___x_1009_);
lean_dec(v___x_1010_);
v___x_1017_ = l_Lean_Syntax_matchesNull(v___x_1016_, v___x_1003_);
if (v___x_1017_ == 0)
{
v___y_999_ = v___x_1017_;
goto v___jp_998_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_lt(v___x_1003_, v___y_993_);
v___y_999_ = v___x_1018_;
goto v___jp_998_;
}
}
}
}
}
}
v___jp_998_:
{
if (v___y_999_ == 0)
{
v_x_994_ = v_tail_997_;
goto _start;
}
else
{
lean_dec(v_tail_997_);
return v___y_999_;
}
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_993_ = stack[0].m_obj;
lean_object* v_x_994_ = stack[1].m_obj;
uint8_t v_res_1019_;
v_res_1019_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___y_993_, v_x_994_);
stack->m_num = v_res_1019_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5___boxed(lean_object* v___y_1020_, lean_object* v_x_1021_){
_start:
{
uint8_t v_res_1022_; lean_object* v_r_1023_; 
v_res_1022_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___y_1020_, v_x_1021_);
lean_dec(v___y_1020_);
v_r_1023_ = lean_box(v_res_1022_);
return v_r_1023_;
}
}
uint8_t l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = 0;
return v___x_1025_;
}
else
{
lean_object* v_head_1026_; lean_object* v_tail_1027_; uint8_t v___x_1028_; 
v_head_1026_ = lean_ctor_get(v_x_1024_, 0);
v_tail_1027_ = lean_ctor_get(v_x_1024_, 1);
v___x_1028_ = l_Lean_isPrivateName(v_head_1026_);
if (v___x_1028_ == 0)
{
v_x_1024_ = v_tail_1027_;
goto _start;
}
else
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1024_ = stack[0].m_obj;
uint8_t v_res_1030_;
v_res_1030_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_x_1024_);
stack->m_num = v_res_1030_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0___boxed(lean_object* v_x_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_x_1031_);
lean_dec(v_x_1031_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(lean_object* v_as_1034_, size_t v_i_1035_, size_t v_stop_1036_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_eq(v_i_1035_, v_stop_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v_ctors_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_array_uget_borrowed(v_as_1034_, v_i_1035_);
v_ctors_1039_ = lean_ctor_get(v___x_1038_, 4);
v___x_1040_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__0(v_ctors_1039_);
if (v___x_1040_ == 0)
{
size_t v___x_1041_; size_t v___x_1042_; 
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1035_, v___x_1041_);
v_i_1035_ = v___x_1042_;
goto _start;
}
else
{
return v___x_1040_;
}
}
else
{
uint8_t v___x_1044_; 
v___x_1044_ = 0;
return v___x_1044_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1034_ = stack[0].m_obj;
size_t v_i_1035_ = stack[1].m_num;
size_t v_stop_1036_ = stack[2].m_num;
uint8_t v_res_1045_;
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_as_1034_, v_i_1035_, v_stop_1036_);
stack->m_num = v_res_1045_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3___boxed(lean_object* v_as_1046_, lean_object* v_i_1047_, lean_object* v_stop_1048_){
_start:
{
size_t v_i_boxed_1049_; size_t v_stop_boxed_1050_; uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_i_boxed_1049_ = lean_unbox_usize(v_i_1047_);
lean_dec(v_i_1047_);
v_stop_boxed_1050_ = lean_unbox_usize(v_stop_1048_);
lean_dec(v_stop_1048_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_as_1046_, v_i_boxed_1049_, v_stop_boxed_1050_);
lean_dec_ref(v_as_1046_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__1));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__3));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object* v_typeName_1061_, lean_object* v_cont_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; 
lean_inc(v_typeName_1061_);
v___x_1066_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1(v_typeName_1061_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v_all_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_all_1068_ = lean_ctor_get(v_a_1067_, 3);
lean_inc(v_all_1068_);
lean_dec(v_a_1067_);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1071_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_all_1068_, v___x_1070_, v_a_1063_, v_a_1064_);
lean_dec(v_all_1068_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_array_get_size(v_a_1072_);
v___x_1074_ = lean_nat_dec_lt(v___x_1069_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v_a_1072_);
lean_dec(v_typeName_1061_);
lean_inc(v_a_1064_);
lean_inc_ref(v_a_1063_);
v___x_1075_ = lean_apply_3(v_cont_1062_, v_a_1063_, v_a_1064_, lean_box(0));
return v___x_1075_;
}
else
{
if (v___x_1074_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_a_1072_);
lean_dec(v_typeName_1061_);
lean_inc(v_a_1064_);
lean_inc_ref(v_a_1063_);
v___x_1076_ = lean_apply_3(v_cont_1062_, v_a_1063_, v_a_1064_, lean_box(0));
return v___x_1076_;
}
else
{
size_t v___x_1077_; size_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = ((size_t)0ULL);
v___x_1078_ = lean_usize_of_nat(v___x_1073_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__3(v_a_1072_, v___x_1077_, v___x_1078_);
lean_dec(v_a_1072_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_typeName_1061_);
lean_inc(v_a_1064_);
lean_inc_ref(v_a_1063_);
v___x_1080_ = lean_apply_3(v_cont_1062_, v_a_1063_, v_a_1064_, lean_box(0));
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___f_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_box(v___x_1079_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1082_, 0, v___x_1081_);
v___x_1083_ = l_Lean_isPrivateName(v_typeName_1061_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Elab_Command_getScope___redArg(v_a_1064_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v_attrs_1086_; uint8_t v___x_1087_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v_attrs_1086_ = lean_ctor_get(v_a_1085_, 9);
lean_inc(v_attrs_1086_);
lean_dec(v_a_1085_);
v___x_1087_ = l_List_any___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__5(v___x_1073_, v_attrs_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v_typeName_1061_);
v___x_1088_ = l_Lean_Elab_Command_withScope___redArg(v___f_1082_, v_cont_1062_, v_a_1063_, v_a_1064_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v___f_1082_);
lean_dec_ref(v_cont_1062_);
v___x_1089_ = lean_obj_once(&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2, &l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2_once, _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__2);
v___x_1090_ = l_Lean_MessageData_ofConstName(v_typeName_1061_, v___x_1083_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4, &l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4_once, _init_l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__4);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v___x_1093_, v_a_1063_, v_a_1064_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v___f_1082_);
lean_dec_ref(v_cont_1062_);
lean_dec(v_typeName_1061_);
v_a_1103_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1084_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1084_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v___x_1111_; 
lean_dec(v_typeName_1061_);
v___x_1111_ = l_Lean_Elab_Command_withScope___redArg(v___f_1082_, v_cont_1062_, v_a_1063_, v_a_1064_);
return v___x_1111_;
}
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v_cont_1062_);
lean_dec(v_typeName_1061_);
v_a_1112_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1071_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1071_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_cont_1062_);
lean_dec(v_typeName_1061_);
v_a_1120_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1066_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1066_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1061_ = stack[0].m_obj;
lean_object* v_cont_1062_ = stack[1].m_obj;
lean_object* v_a_1063_ = stack[2].m_obj;
lean_object* v_a_1064_ = stack[3].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1061_, v_cont_1062_, v_a_1063_, v_a_1064_);
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___boxed(lean_object* v_typeName_1129_, lean_object* v_cont_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1129_, v_cont_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1134_;
}
}
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors(lean_object* v_00_u03b1_1135_, lean_object* v_typeName_1136_, lean_object* v_cont_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_typeName_1136_, v_cont_1137_, v_a_1138_, v_a_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_withoutExposeFromCtors_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_1136_ = stack[1].m_obj;
lean_object* v_cont_1137_ = stack[2].m_obj;
lean_object* v_a_1138_ = stack[3].m_obj;
lean_object* v_a_1139_ = stack[4].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l_Lean_Elab_Deriving_withoutExposeFromCtors(lean_box(0), v_typeName_1136_, v_cont_1137_, v_a_1138_, v_a_1139_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_typeName_1144_, lean_object* v_cont_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_Deriving_withoutExposeFromCtors(v_00_u03b1_1143_, v_typeName_1144_, v_cont_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1149_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(lean_object* v_as_1150_, lean_object* v_as_x27_1151_, lean_object* v_b_1152_, lean_object* v_a_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___redArg(v_as_x27_1151_, v_b_1152_, v___y_1154_, v___y_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1150_ = stack[0].m_obj;
lean_object* v_as_x27_1151_ = stack[1].m_obj;
lean_object* v_b_1152_ = stack[2].m_obj;
lean_object* v___y_1154_ = stack[4].m_obj;
lean_object* v___y_1155_ = stack[5].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(v_as_1150_, v_as_x27_1151_, v_b_1152_, lean_box(0), v___y_1154_, v___y_1155_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2___boxed(lean_object* v_as_1159_, lean_object* v_as_x27_1160_, lean_object* v_b_1161_, lean_object* v_a_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__2(v_as_1159_, v_as_x27_1160_, v_b_1161_, v_a_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v_as_x27_1160_);
lean_dec(v_as_1159_);
return v_res_1166_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(lean_object* v_msgData_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___redArg(v_msgData_1167_, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1167_ = stack[0].m_obj;
lean_object* v___y_1168_ = stack[1].m_obj;
lean_object* v___y_1169_ = stack[2].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(v_msgData_1167_, v___y_1168_, v___y_1169_);
stack->m_obj
 = v_res_1172_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6___boxed(lean_object* v_msgData_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__6(v_msgData_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1177_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(lean_object* v_00_u03b1_1178_, lean_object* v_msg_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___redArg(v_msg_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1179_ = stack[1].m_obj;
lean_object* v___y_1180_ = stack[2].m_obj;
lean_object* v___y_1181_ = stack[3].m_obj;
lean_object* v_res_1184_;
v_res_1184_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(lean_box(0), v_msg_1179_, v___y_1180_, v___y_1181_);
stack->m_obj
 = v_res_1184_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6(v_00_u03b1_1185_, v_msg_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1190_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(lean_object* v_msgData_1191_, lean_object* v_macroStack_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg(v_msgData_1191_, v_macroStack_1192_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1191_ = stack[0].m_obj;
lean_object* v_macroStack_1192_ = stack[1].m_obj;
lean_object* v___y_1193_ = stack[2].m_obj;
lean_object* v___y_1194_ = stack[3].m_obj;
lean_object* v_res_1197_;
v_res_1197_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(v_msgData_1191_, v_macroStack_1192_, v___y_1193_, v___y_1194_);
stack->m_obj
 = v_res_1197_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___boxed(lean_object* v_msgData_1198_, lean_object* v_macroStack_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7(v_msgData_1198_, v_macroStack_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1203_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_bs_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_usize_dec_lt(v_i_1205_, v_sz_1204_);
if (v___x_1207_ == 0)
{
return v_bs_1206_;
}
else
{
lean_object* v_v_1208_; lean_object* v___x_1209_; lean_object* v_bs_x27_1210_; size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v_v_1208_ = lean_array_uget(v_bs_1206_, v_i_1205_);
v___x_1209_ = lean_unsigned_to_nat(0u);
v_bs_x27_1210_ = lean_array_uset(v_bs_1206_, v_i_1205_, v___x_1209_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1205_, v___x_1211_);
v___x_1213_ = lean_array_uset(v_bs_x27_1210_, v_i_1205_, v_v_1208_);
v_i_1205_ = v___x_1212_;
v_bs_1206_ = v___x_1213_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1204_ = stack[0].m_num;
size_t v_i_1205_ = stack[1].m_num;
lean_object* v_bs_1206_ = stack[2].m_obj;
lean_object* v_res_1215_;
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_1204_, v_i_1205_, v_bs_1206_);
stack->m_obj
 = v_res_1215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1___boxed(lean_object* v_sz_1216_, lean_object* v_i_1217_, lean_object* v_bs_1218_){
_start:
{
size_t v_sz_boxed_1219_; size_t v_i_boxed_1220_; lean_object* v_res_1221_; 
v_sz_boxed_1219_ = lean_unbox_usize(v_sz_1216_);
lean_dec(v_sz_1216_);
v_i_boxed_1220_ = lean_unbox_usize(v_i_1217_);
lean_dec(v_i_1217_);
v_res_1221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_boxed_1219_, v_i_boxed_1220_, v_bs_1218_);
return v_res_1221_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(lean_object* v_msgData_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v_env_1229_; uint8_t v___x_1230_; lean_object* v_env_1231_; lean_object* v___x_1232_; lean_object* v_toCold_1233_; lean_object* v_mctx_1234_; lean_object* v_lctx_1235_; lean_object* v_options_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1228_ = lean_st_ref_get(v___y_1226_);
v_env_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_ref(v_env_1229_);
lean_dec(v___x_1228_);
v___x_1230_ = 0;
v_env_1231_ = l_Lean_Environment_setRecordingDeps(v_env_1229_, v___x_1230_);
v___x_1232_ = lean_st_ref_get(v___y_1224_);
v_toCold_1233_ = lean_ctor_get(v___y_1225_, 0);
v_mctx_1234_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref(v_mctx_1234_);
lean_dec(v___x_1232_);
v_lctx_1235_ = lean_ctor_get(v___y_1223_, 2);
v_options_1236_ = lean_ctor_get(v_toCold_1233_, 2);
lean_inc_ref(v_options_1236_);
lean_inc_ref(v_lctx_1235_);
v___x_1237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1237_, 0, v_env_1231_);
lean_ctor_set(v___x_1237_, 1, v_mctx_1234_);
lean_ctor_set(v___x_1237_, 2, v_lctx_1235_);
lean_ctor_set(v___x_1237_, 3, v_options_1236_);
v___x_1238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_msgData_1222_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1222_ = stack[0].m_obj;
lean_object* v___y_1223_ = stack[1].m_obj;
lean_object* v___y_1224_ = stack[2].m_obj;
lean_object* v___y_1225_ = stack[3].m_obj;
lean_object* v___y_1226_ = stack[4].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
stack->m_obj
 = v_res_1240_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msgData_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1247_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_1248_, lean_object* v_macroStack_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1250_);
v___x_1253_ = l_Lean_Elab_pp_macroStack;
v___x_1254_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__8(v___x_1252_, v___x_1253_);
lean_dec_ref(v___x_1252_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec(v_macroStack_1249_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_msgData_1248_);
return v___x_1255_;
}
else
{
if (lean_obj_tag(v_macroStack_1249_) == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_msgData_1248_);
return v___x_1256_;
}
else
{
lean_object* v_head_1257_; lean_object* v_after_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1273_; 
v_head_1257_ = lean_ctor_get(v_macroStack_1249_, 0);
lean_inc(v_head_1257_);
v_after_1258_ = lean_ctor_get(v_head_1257_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_head_1257_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_head_1257_, 0);
lean_dec(v_unused_1274_);
v___x_1260_ = v_head_1257_;
v_isShared_1261_ = v_isSharedCheck_1273_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_after_1258_);
lean_dec(v_head_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1273_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9___closed__0);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 7);
lean_ctor_set(v___x_1260_, 1, v___x_1262_);
lean_ctor_set(v___x_1260_, 0, v_msgData_1248_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_msgData_1248_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_msgData_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1265_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7___redArg___closed__2);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_MessageData_ofSyntax(v_after_1258_);
v___x_1268_ = l_Lean_indentD(v___x_1267_);
v_msgData_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1269_, 0, v___x_1266_);
lean_ctor_set(v_msgData_1269_, 1, v___x_1268_);
v___x_1270_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__6_spec__7_spec__9(v_msgData_1269_, v_macroStack_1249_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1248_ = stack[0].m_obj;
lean_object* v_macroStack_1249_ = stack[1].m_obj;
lean_object* v___y_1250_ = stack[2].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1248_, v_macroStack_1249_, v___y_1250_);
stack->m_obj
 = v_res_1275_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_1276_, lean_object* v_macroStack_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1276_, v_macroStack_1277_, v___y_1278_);
lean_dec_ref(v___y_1278_);
return v_res_1280_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(lean_object* v_msg_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_ref_1289_; lean_object* v_macroStack_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1294_; lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
v_ref_1289_ = lean_ctor_get(v___y_1286_, 2);
v_macroStack_1290_ = lean_ctor_get(v___y_1282_, 1);
v___x_1291_ = l_Lean_Elab_getBetterRef(v_ref_1289_, v_macroStack_1290_);
v___x_1292_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1281_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
lean_inc(v_macroStack_1290_);
v___x_1294_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_a_1293_, v_macroStack_1290_, v___y_1286_);
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1291_);
lean_ctor_set(v___x_1299_, 1, v_a_1295_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1281_ = stack[0].m_obj;
lean_object* v___y_1282_ = stack[1].m_obj;
lean_object* v___y_1283_ = stack[2].m_obj;
lean_object* v___y_1284_ = stack[3].m_obj;
lean_object* v___y_1285_ = stack[4].m_obj;
lean_object* v___y_1286_ = stack[5].m_obj;
lean_object* v___y_1287_ = stack[6].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1313_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(lean_object* v_constName_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v_env_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_st_ref_get(v___y_1320_);
v_env_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc_ref(v_env_1323_);
lean_dec(v___x_1322_);
lean_inc(v_constName_1314_);
v___x_1324_ = l_Lean_isInductiveCore_x3f(v_env_1323_, v_constName_1314_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1325_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__1);
v___x_1326_ = 0;
v___x_1327_ = l_Lean_MessageData_ofConstName(v_constName_1314_, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1325_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__1___closed__3);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v___x_1330_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1331_;
}
else
{
lean_object* v_val_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v_constName_1314_);
v_val_1332_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1324_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_val_1332_);
lean_dec(v___x_1324_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 0);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_val_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1314_ = stack[0].m_obj;
lean_object* v___y_1315_ = stack[1].m_obj;
lean_object* v___y_1316_ = stack[2].m_obj;
lean_object* v___y_1317_ = stack[3].m_obj;
lean_object* v___y_1318_ = stack[4].m_obj;
lean_object* v___y_1319_ = stack[5].m_obj;
lean_object* v___y_1320_ = stack[6].m_obj;
lean_object* v_res_1340_;
v_res_1340_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_constName_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
stack->m_obj
 = v_res_1340_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0___boxed(lean_object* v_constName_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_constName_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1349_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object* v_className_1351_, lean_object* v_indName_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_indName_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc_n(v_a_1361_, 2);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_1361_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc_n(v_a_1363_, 2);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_1363_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v_a_1367_; lean_object* v_ref_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; size_t v_sz_1377_; size_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_1361_, v_a_1363_, v_a_1357_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref(v___x_1366_);
v_ref_1368_ = lean_ctor_get(v_a_1357_, 2);
v___x_1369_ = 0;
v___x_1370_ = l_Lean_SourceInfo_fromRef(v_ref_1368_, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
v___x_1372_ = l_Lean_mkCIdent(v_className_1351_);
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1370_);
v___x_1374_ = l_Lean_Syntax_node1(v___x_1370_, v___x_1373_, v_a_1367_);
v___x_1375_ = l_Lean_Syntax_node2(v___x_1370_, v___x_1371_, v___x_1372_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstName___closed__0));
v_sz_1377_ = lean_array_size(v_a_1365_);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkInstName_spec__1(v_sz_1377_, v___x_1378_, v_a_1365_);
v___x_1380_ = l_Lean_Elab_Command_NameGen_mkBaseNameWithSuffix_x27(v___x_1376_, v___x_1379_, v___x_1375_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
return v___x_1380_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1363_);
lean_dec(v_a_1361_);
lean_dec(v_className_1351_);
v_a_1381_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1364_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1364_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_a_1361_);
lean_dec(v_className_1351_);
v_a_1389_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1362_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1362_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_className_1351_);
v_a_1397_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1360_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1360_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInstName_0interp(lean_interpreter_value* stack)
{
lean_object* v_className_1351_ = stack[0].m_obj;
lean_object* v_indName_1352_ = stack[1].m_obj;
lean_object* v_a_1353_ = stack[2].m_obj;
lean_object* v_a_1354_ = stack[3].m_obj;
lean_object* v_a_1355_ = stack[4].m_obj;
lean_object* v_a_1356_ = stack[5].m_obj;
lean_object* v_a_1357_ = stack[6].m_obj;
lean_object* v_a_1358_ = stack[7].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_Elab_Deriving_mkInstName(v_className_1351_, v_indName_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstName___boxed(lean_object* v_className_1406_, lean_object* v_indName_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Elab_Deriving_mkInstName(v_className_1406_, v_indName_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1415_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(lean_object* v_00_u03b1_1416_, lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___redArg(v_msg_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1417_ = stack[1].m_obj;
lean_object* v___y_1418_ = stack[2].m_obj;
lean_object* v___y_1419_ = stack[3].m_obj;
lean_object* v___y_1420_ = stack[4].m_obj;
lean_object* v___y_1421_ = stack[5].m_obj;
lean_object* v___y_1422_ = stack[6].m_obj;
lean_object* v___y_1423_ = stack[7].m_obj;
lean_object* v_res_1426_;
v_res_1426_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(lean_box(0), v_msg_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
stack->m_obj
 = v_res_1426_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0(v_00_u03b1_1427_, v_msg_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1436_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(lean_object* v_msgData_1437_, lean_object* v_macroStack_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___redArg(v_msgData_1437_, v_macroStack_1438_, v___y_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1437_ = stack[0].m_obj;
lean_object* v_macroStack_1438_ = stack[1].m_obj;
lean_object* v___y_1439_ = stack[2].m_obj;
lean_object* v___y_1440_ = stack[3].m_obj;
lean_object* v___y_1441_ = stack[4].m_obj;
lean_object* v___y_1442_ = stack[5].m_obj;
lean_object* v___y_1443_ = stack[6].m_obj;
lean_object* v___y_1444_ = stack[7].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_1437_, v_macroStack_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1448_, lean_object* v_macroStack_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__2(v_msgData_1448_, v_macroStack_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1457_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(lean_object* v_as_x27_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
if (lean_obj_tag(v_as_x27_1458_) == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1459_);
return v___x_1467_;
}
else
{
lean_object* v_head_1468_; lean_object* v_tail_1469_; lean_object* v___x_1470_; 
v_head_1468_ = lean_ctor_get(v_as_x27_1458_, 0);
v_tail_1469_ = lean_ctor_get(v_as_x27_1458_, 1);
lean_inc(v_head_1468_);
v___x_1470_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_head_1468_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_array_push(v_b_1459_, v_a_1471_);
v_as_x27_1458_ = v_tail_1469_;
v_b_1459_ = v___x_1472_;
goto _start;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_b_1459_);
v_a_1474_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1470_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1458_ = stack[0].m_obj;
lean_object* v_b_1459_ = stack[1].m_obj;
lean_object* v___y_1460_ = stack[2].m_obj;
lean_object* v___y_1461_ = stack[3].m_obj;
lean_object* v___y_1462_ = stack[4].m_obj;
lean_object* v___y_1463_ = stack[5].m_obj;
lean_object* v___y_1464_ = stack[6].m_obj;
lean_object* v___y_1465_ = stack[7].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1458_, v_b_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg___boxed(lean_object* v_as_x27_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1483_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_as_x27_1483_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
if (lean_obj_tag(v_a_1493_) == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = l_List_reverse___redArg(v_a_1494_);
return v___x_1495_;
}
else
{
lean_object* v_head_1496_; lean_object* v_tail_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1506_; 
v_head_1496_ = lean_ctor_get(v_a_1493_, 0);
v_tail_1497_ = lean_ctor_get(v_a_1493_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_a_1493_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1499_ = v_a_1493_;
v_isShared_1500_ = v_isSharedCheck_1506_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_tail_1497_);
lean_inc(v_head_1496_);
lean_dec(v_a_1493_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1506_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = l_Lean_MessageData_ofName(v_head_1496_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v_a_1494_);
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_a_1494_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
v_a_1493_ = v_tail_1497_;
v_a_1494_ = v___x_1503_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1507_; double v___x_1508_; 
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_float_of_nat(v___x_1507_);
return v___x_1508_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(lean_object* v_cls_1512_, lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_ref_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1566_; 
v_ref_1519_ = lean_ctor_get(v___y_1516_, 2);
v___x_1520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0_spec__0_spec__1(v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1566_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1566_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v_traceState_1526_; lean_object* v_env_1527_; lean_object* v_nextMacroScope_1528_; lean_object* v_ngen_1529_; lean_object* v_auxDeclNGen_1530_; lean_object* v_cache_1531_; lean_object* v_recordedDeps_1532_; lean_object* v_messages_1533_; lean_object* v_infoState_1534_; lean_object* v_snapshotTasks_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1565_; 
v___x_1525_ = lean_st_ref_take(v___y_1517_);
v_traceState_1526_ = lean_ctor_get(v___x_1525_, 4);
v_env_1527_ = lean_ctor_get(v___x_1525_, 0);
v_nextMacroScope_1528_ = lean_ctor_get(v___x_1525_, 1);
v_ngen_1529_ = lean_ctor_get(v___x_1525_, 2);
v_auxDeclNGen_1530_ = lean_ctor_get(v___x_1525_, 3);
v_cache_1531_ = lean_ctor_get(v___x_1525_, 5);
v_recordedDeps_1532_ = lean_ctor_get(v___x_1525_, 6);
v_messages_1533_ = lean_ctor_get(v___x_1525_, 7);
v_infoState_1534_ = lean_ctor_get(v___x_1525_, 8);
v_snapshotTasks_1535_ = lean_ctor_get(v___x_1525_, 9);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1537_ = v___x_1525_;
v_isShared_1538_ = v_isSharedCheck_1565_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snapshotTasks_1535_);
lean_inc(v_infoState_1534_);
lean_inc(v_messages_1533_);
lean_inc(v_recordedDeps_1532_);
lean_inc(v_cache_1531_);
lean_inc(v_traceState_1526_);
lean_inc(v_auxDeclNGen_1530_);
lean_inc(v_ngen_1529_);
lean_inc(v_nextMacroScope_1528_);
lean_inc(v_env_1527_);
lean_dec(v___x_1525_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1565_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
uint64_t v_tid_1539_; lean_object* v_traces_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1564_; 
v_tid_1539_ = lean_ctor_get_uint64(v_traceState_1526_, sizeof(void*)*1);
v_traces_1540_ = lean_ctor_get(v_traceState_1526_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_traceState_1526_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1542_ = v_traceState_1526_;
v_isShared_1543_ = v_isSharedCheck_1564_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_traces_1540_);
lean_dec(v_traceState_1526_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1564_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; double v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__0);
v___x_1547_ = 0;
v___x_1548_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__1));
v___x_1549_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1549_, 0, v_cls_1512_);
lean_ctor_set(v___x_1549_, 1, v___x_1545_);
lean_ctor_set(v___x_1549_, 2, v___x_1548_);
lean_ctor_set_float(v___x_1549_, sizeof(void*)*3, v___x_1546_);
lean_ctor_set_float(v___x_1549_, sizeof(void*)*3 + 8, v___x_1546_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*3 + 16, v___x_1547_);
v___x_1550_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___closed__2));
v___x_1551_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v_a_1521_);
lean_ctor_set(v___x_1551_, 2, v___x_1550_);
lean_inc(v_ref_1519_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_ref_1519_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_PersistentArray_push___redArg(v_traces_1540_, v___x_1552_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1553_);
v___x_1555_ = v___x_1542_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1553_);
lean_ctor_set_uint64(v_reuseFailAlloc_1563_, sizeof(void*)*1, v_tid_1539_);
v___x_1555_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 4, v___x_1555_);
v___x_1557_ = v___x_1537_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_env_1527_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_nextMacroScope_1528_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_ngen_1529_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_auxDeclNGen_1530_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1562_, 5, v_cache_1531_);
lean_ctor_set(v_reuseFailAlloc_1562_, 6, v_recordedDeps_1532_);
lean_ctor_set(v_reuseFailAlloc_1562_, 7, v_messages_1533_);
lean_ctor_set(v_reuseFailAlloc_1562_, 8, v_infoState_1534_);
lean_ctor_set(v_reuseFailAlloc_1562_, 9, v_snapshotTasks_1535_);
v___x_1557_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_st_ref_put(v___y_1517_, v___x_1557_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1544_);
v___x_1560_ = v___x_1523_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1544_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1512_ = stack[0].m_obj;
lean_object* v_msg_1513_ = stack[1].m_obj;
lean_object* v___y_1514_ = stack[2].m_obj;
lean_object* v___y_1515_ = stack[3].m_obj;
lean_object* v___y_1516_ = stack[4].m_obj;
lean_object* v___y_1517_ = stack[5].m_obj;
lean_object* v_res_1567_;
v_res_1567_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1512_, v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
stack->m_obj
 = v_res_1567_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg___boxed(lean_object* v_cls_1568_, lean_object* v_msg_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1568_, v_msg_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1575_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(lean_object* v_fnPrefix_1577_, lean_object* v_a_1578_, lean_object* v_range_1579_, lean_object* v_b_1580_, lean_object* v_i_1581_){
_start:
{
lean_object* v_stop_1583_; lean_object* v_step_1584_; uint8_t v___x_1585_; 
v_stop_1583_ = lean_ctor_get(v_range_1579_, 1);
v_step_1584_ = lean_ctor_get(v_range_1579_, 2);
v___x_1585_ = lean_nat_dec_lt(v_i_1581_, v_stop_1583_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec(v_i_1581_);
lean_dec(v_a_1578_);
lean_dec_ref(v_fnPrefix_1577_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_b_1580_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___closed__0));
lean_inc_ref(v_fnPrefix_1577_);
v___x_1589_ = lean_string_append(v_fnPrefix_1577_, v___x_1588_);
v___x_1590_ = lean_nat_add(v_i_1581_, v___x_1587_);
v___x_1591_ = l_Nat_reprFast(v___x_1590_);
v___x_1592_ = lean_string_append(v___x_1589_, v___x_1591_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = lean_box(0);
v___x_1594_ = l_Lean_Name_str___override(v___x_1593_, v___x_1592_);
lean_inc(v_a_1578_);
v___x_1595_ = l_Lean_Name_append(v_a_1578_, v___x_1594_);
v___x_1596_ = lean_array_push(v_b_1580_, v___x_1595_);
v___x_1597_ = lean_nat_add(v_i_1581_, v_step_1584_);
lean_dec(v_i_1581_);
v_b_1580_ = v___x_1596_;
v_i_1581_ = v___x_1597_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnPrefix_1577_ = stack[0].m_obj;
lean_object* v_a_1578_ = stack[1].m_obj;
lean_object* v_range_1579_ = stack[2].m_obj;
lean_object* v_b_1580_ = stack[3].m_obj;
lean_object* v_i_1581_ = stack[4].m_obj;
lean_object* v_res_1599_;
v_res_1599_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1577_, v_a_1578_, v_range_1579_, v_b_1580_, v_i_1581_);
stack->m_obj
 = v_res_1599_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg___boxed(lean_object* v_fnPrefix_1600_, lean_object* v_a_1601_, lean_object* v_range_1602_, lean_object* v_b_1603_, lean_object* v_i_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1600_, v_a_1601_, v_range_1602_, v_b_1603_, v_i_1604_);
lean_dec_ref(v_range_1602_);
return v_res_1606_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__5(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1616_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__4));
v___x_1617_ = l_Lean_Name_append(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__7(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__6));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_mkContext___closed__9(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__8));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object* v_className_1624_, lean_object* v_fnPrefix_1625_, lean_object* v_typeName_1626_, uint8_t v_supportsRec_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc(v_typeName_1626_);
v___x_1635_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_mkInstName_spec__0(v_typeName_1626_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v_all_1637_; uint8_t v_isRec_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v_all_1637_ = lean_ctor_get(v_a_1636_, 3);
v_isRec_1638_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*6);
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = ((lean_object*)(l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg___closed__0));
v___x_1641_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_all_1637_, v___x_1640_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1643_ = l_Lean_Elab_Deriving_mkInstName(v_className_1624_, v_typeName_1626_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1708_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1708_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1708_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___y_1649_; uint8_t v___y_1650_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1659_; lean_object* v_auxFunNames_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = l_List_lengthTR___redArg(v_all_1637_);
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = lean_nat_dec_eq(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_a_1703_; 
v___x_1701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1639_);
lean_ctor_set(v___x_1701_, 1, v___x_1698_);
lean_ctor_set(v___x_1701_, 2, v___x_1699_);
lean_inc(v_a_1644_);
v___x_1702_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1625_, v_a_1644_, v___x_1701_, v___x_1640_, v___x_1639_);
lean_dec_ref_known(v___x_1701_, 3);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v_auxFunNames_1665_ = v_a_1703_;
v___y_1666_ = v_a_1628_;
v___y_1667_ = v_a_1629_;
v___y_1668_ = v_a_1630_;
v___y_1669_ = v_a_1631_;
v___y_1670_ = v_a_1632_;
v___y_1671_ = v_a_1633_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v___x_1698_);
v___x_1704_ = lean_box(0);
v___x_1705_ = l_Lean_Name_str___override(v___x_1704_, v_fnPrefix_1625_);
lean_inc(v_a_1644_);
v___x_1706_ = l_Lean_Name_append(v_a_1644_, v___x_1705_);
v___x_1707_ = lean_array_push(v___x_1640_, v___x_1706_);
v_auxFunNames_1665_ = v___x_1707_;
v___y_1666_ = v_a_1628_;
v___y_1667_ = v_a_1629_;
v___y_1668_ = v_a_1630_;
v___y_1669_ = v_a_1631_;
v___y_1670_ = v_a_1632_;
v___y_1671_ = v_a_1633_;
goto v___jp_1664_;
}
v___jp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1651_, 0, v_a_1644_);
lean_ctor_set(v___x_1651_, 1, v_a_1642_);
lean_ctor_set(v___x_1651_, 2, v___y_1649_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*3, v___y_1650_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1651_);
v___x_1653_ = v___x_1646_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
v___jp_1655_:
{
if (v___y_1657_ == 0)
{
if (v_isRec_1638_ == 0)
{
v___y_1649_ = v___y_1656_;
v___y_1650_ = v_isRec_1638_;
goto v___jp_1648_;
}
else
{
if (v_supportsRec_1627_ == 0)
{
v___y_1649_ = v___y_1656_;
v___y_1650_ = v_isRec_1638_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v___y_1656_;
v___y_1650_ = v___y_1657_;
goto v___jp_1648_;
}
}
}
else
{
v___y_1649_ = v___y_1656_;
v___y_1650_ = v___y_1657_;
goto v___jp_1648_;
}
}
v___jp_1658_:
{
uint8_t v___x_1660_; 
v___x_1660_ = l_Lean_InductiveVal_isNested(v_a_1636_);
lean_dec(v_a_1636_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_array_get_size(v_a_1642_);
v___x_1663_ = lean_nat_dec_lt(v___x_1661_, v___x_1662_);
v___y_1656_ = v___y_1659_;
v___y_1657_ = v___x_1663_;
goto v___jp_1655_;
}
else
{
v___y_1656_ = v___y_1659_;
v___y_1657_ = v___x_1660_;
goto v___jp_1655_;
}
}
v___jp_1664_:
{
lean_object* v_toCold_1672_; lean_object* v_options_1673_; uint8_t v_hasTrace_1674_; 
v_toCold_1672_ = lean_ctor_get(v___y_1670_, 0);
v_options_1673_ = lean_ctor_get(v_toCold_1672_, 2);
v_hasTrace_1674_ = lean_ctor_get_uint8(v_options_1673_, sizeof(void*)*1);
if (v_hasTrace_1674_ == 0)
{
v___y_1659_ = v_auxFunNames_1665_;
goto v___jp_1658_;
}
else
{
lean_object* v_inheritedTraceOptions_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_inheritedTraceOptions_1675_ = lean_ctor_get(v_toCold_1672_, 11);
v___x_1676_ = ((lean_object*)(l_Lean_Elab_Deriving_mkContext___closed__2));
v___x_1677_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__5, &l_Lean_Elab_Deriving_mkContext___closed__5_once, _init_l_Lean_Elab_Deriving_mkContext___closed__5);
v___x_1678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1675_, v_options_1673_, v___x_1677_);
if (v___x_1678_ == 0)
{
v___y_1659_ = v_auxFunNames_1665_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__7, &l_Lean_Elab_Deriving_mkContext___closed__7_once, _init_l_Lean_Elab_Deriving_mkContext___closed__7);
lean_inc(v_a_1644_);
v___x_1680_ = l_Lean_MessageData_ofName(v_a_1644_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_obj_once(&l_Lean_Elab_Deriving_mkContext___closed__9, &l_Lean_Elab_Deriving_mkContext___closed__9_once, _init_l_Lean_Elab_Deriving_mkContext___closed__9);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_inc_ref(v_auxFunNames_1665_);
v___x_1684_ = lean_array_to_list(v_auxFunNames_1665_);
v___x_1685_ = lean_box(0);
v___x_1686_ = l_List_mapTR_loop___at___00Lean_Elab_Deriving_mkContext_spec__1(v___x_1684_, v___x_1685_);
v___x_1687_ = l_Lean_MessageData_ofList(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1683_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v___x_1676_, v___x_1688_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec_ref_known(v___x_1689_, 1);
v___y_1659_ = v_auxFunNames_1665_;
goto v___jp_1658_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref(v_auxFunNames_1665_);
lean_del_object(v___x_1646_);
lean_dec(v_a_1644_);
lean_dec(v_a_1642_);
lean_dec(v_a_1636_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
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
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_a_1642_);
lean_dec(v_a_1636_);
lean_dec_ref(v_fnPrefix_1625_);
v_a_1709_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1643_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1643_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1636_);
lean_dec(v_typeName_1626_);
lean_dec_ref(v_fnPrefix_1625_);
lean_dec(v_className_1624_);
v_a_1717_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1641_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1641_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_typeName_1626_);
lean_dec_ref(v_fnPrefix_1625_);
lean_dec(v_className_1624_);
v_a_1725_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1635_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1635_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_className_1624_ = stack[0].m_obj;
lean_object* v_fnPrefix_1625_ = stack[1].m_obj;
lean_object* v_typeName_1626_ = stack[2].m_obj;
uint8_t v_supportsRec_1627_ = stack[3].m_num;
lean_object* v_a_1628_ = stack[4].m_obj;
lean_object* v_a_1629_ = stack[5].m_obj;
lean_object* v_a_1630_ = stack[6].m_obj;
lean_object* v_a_1631_ = stack[7].m_obj;
lean_object* v_a_1632_ = stack[8].m_obj;
lean_object* v_a_1633_ = stack[9].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l_Lean_Elab_Deriving_mkContext(v_className_1624_, v_fnPrefix_1625_, v_typeName_1626_, v_supportsRec_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkContext___boxed(lean_object* v_className_1734_, lean_object* v_fnPrefix_1735_, lean_object* v_typeName_1736_, lean_object* v_supportsRec_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
uint8_t v_supportsRec_boxed_1745_; lean_object* v_res_1746_; 
v_supportsRec_boxed_1745_ = lean_unbox(v_supportsRec_1737_);
v_res_1746_ = l_Lean_Elab_Deriving_mkContext(v_className_1734_, v_fnPrefix_1735_, v_typeName_1736_, v_supportsRec_boxed_1745_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
return v_res_1746_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(lean_object* v_as_1747_, lean_object* v_as_x27_1748_, lean_object* v_b_1749_, lean_object* v_a_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___redArg(v_as_x27_1748_, v_b_1749_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1747_ = stack[0].m_obj;
lean_object* v_as_x27_1748_ = stack[1].m_obj;
lean_object* v_b_1749_ = stack[2].m_obj;
lean_object* v___y_1751_ = stack[4].m_obj;
lean_object* v___y_1752_ = stack[5].m_obj;
lean_object* v___y_1753_ = stack[6].m_obj;
lean_object* v___y_1754_ = stack[7].m_obj;
lean_object* v___y_1755_ = stack[8].m_obj;
lean_object* v___y_1756_ = stack[9].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(v_as_1747_, v_as_x27_1748_, v_b_1749_, lean_box(0), v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0___boxed(lean_object* v_as_1760_, lean_object* v_as_x27_1761_, lean_object* v_b_1762_, lean_object* v_a_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_List_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__0(v_as_1760_, v_as_x27_1761_, v_b_1762_, v_a_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v_as_x27_1761_);
lean_dec(v_as_1760_);
return v_res_1771_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(lean_object* v_cls_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___redArg(v_cls_1772_, v_msg_1773_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1772_ = stack[0].m_obj;
lean_object* v_msg_1773_ = stack[1].m_obj;
lean_object* v___y_1774_ = stack[2].m_obj;
lean_object* v___y_1775_ = stack[3].m_obj;
lean_object* v___y_1776_ = stack[4].m_obj;
lean_object* v___y_1777_ = stack[5].m_obj;
lean_object* v___y_1778_ = stack[6].m_obj;
lean_object* v___y_1779_ = stack[7].m_obj;
lean_object* v_res_1782_;
v_res_1782_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(v_cls_1772_, v_msg_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
stack->m_obj
 = v_res_1782_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2___boxed(lean_object* v_cls_1783_, lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_addTrace___at___00Lean_Elab_Deriving_mkContext_spec__2(v_cls_1783_, v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1792_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(lean_object* v_fnPrefix_1793_, lean_object* v_a_1794_, lean_object* v_range_1795_, lean_object* v_b_1796_, lean_object* v_i_1797_, lean_object* v_hs_1798_, lean_object* v_hl_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___redArg(v_fnPrefix_1793_, v_a_1794_, v_range_1795_, v_b_1796_, v_i_1797_);
return v___x_1807_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnPrefix_1793_ = stack[0].m_obj;
lean_object* v_a_1794_ = stack[1].m_obj;
lean_object* v_range_1795_ = stack[2].m_obj;
lean_object* v_b_1796_ = stack[3].m_obj;
lean_object* v_i_1797_ = stack[4].m_obj;
lean_object* v___y_1800_ = stack[7].m_obj;
lean_object* v___y_1801_ = stack[8].m_obj;
lean_object* v___y_1802_ = stack[9].m_obj;
lean_object* v___y_1803_ = stack[10].m_obj;
lean_object* v___y_1804_ = stack[11].m_obj;
lean_object* v___y_1805_ = stack[12].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_1793_, v_a_1794_, v_range_1795_, v_b_1796_, v_i_1797_, lean_box(0), lean_box(0), v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3___boxed(lean_object* v_fnPrefix_1809_, lean_object* v_a_1810_, lean_object* v_range_1811_, lean_object* v_b_1812_, lean_object* v_i_1813_, lean_object* v_hs_1814_, lean_object* v_hl_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Deriving_mkContext_spec__3(v_fnPrefix_1809_, v_a_1810_, v_range_1811_, v_b_1812_, v_i_1813_, v_hs_1814_, v_hl_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_range_1811_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_1824_, lean_object* v_b_1825_){
_start:
{
lean_object* v_array_1826_; lean_object* v_start_1827_; lean_object* v_stop_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1841_; 
v_array_1826_ = lean_ctor_get(v_a_1824_, 0);
v_start_1827_ = lean_ctor_get(v_a_1824_, 1);
v_stop_1828_ = lean_ctor_get(v_a_1824_, 2);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_a_1824_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1830_ = v_a_1824_;
v_isShared_1831_ = v_isSharedCheck_1841_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_stop_1828_);
lean_inc(v_start_1827_);
lean_inc(v_array_1826_);
lean_dec(v_a_1824_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1841_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_nat_dec_lt(v_start_1827_, v_stop_1828_);
if (v___x_1832_ == 0)
{
lean_del_object(v___x_1830_);
lean_dec(v_stop_1828_);
lean_dec(v_start_1827_);
lean_dec_ref(v_array_1826_);
return v_b_1825_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1833_ = lean_unsigned_to_nat(1u);
v___x_1834_ = lean_nat_add(v_start_1827_, v___x_1833_);
lean_inc_ref(v_array_1826_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v___x_1834_);
v___x_1836_ = v___x_1830_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_array_1826_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_stop_1828_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_array_fget(v_array_1826_, v_start_1827_);
lean_dec(v_start_1827_);
lean_dec_ref(v_array_1826_);
v___x_1838_ = lean_array_push(v_b_1825_, v___x_1837_);
v_a_1824_ = v___x_1836_;
v_b_1825_ = v___x_1838_;
goto _start;
}
}
}
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_ref_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_ref_1849_ = lean_ctor_get(v___y_1846_, 2);
v___x_1850_ = 0;
v___x_1851_ = l_Lean_SourceInfo_fromRef(v_ref_1849_, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1842_ = stack[0].m_obj;
lean_object* v___y_1843_ = stack[1].m_obj;
lean_object* v___y_1844_ = stack[2].m_obj;
lean_object* v___y_1845_ = stack[3].m_obj;
lean_object* v___y_1846_ = stack[4].m_obj;
lean_object* v___y_1847_ = stack[5].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0___boxed(lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
return v_res_1861_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(lean_object* v_upperBound_1899_, lean_object* v___x_1900_, lean_object* v_ctx_1901_, lean_object* v_argNames_1902_, lean_object* v_className_1903_, lean_object* v_a_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_nat_dec_lt(v_a_1904_, v_upperBound_1899_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_b_1905_);
return v___x_1914_;
}
else
{
lean_object* v_auxFunNames_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_auxFunNames_1915_ = lean_ctor_get(v_ctx_1901_, 2);
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_array_fget_borrowed(v___x_1900_, v_a_1904_);
v___x_1918_ = lean_array_get_borrowed(v___x_1916_, v_auxFunNames_1915_, v_a_1904_);
lean_inc(v___x_1917_);
v___x_1919_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_1917_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_numParams_1921_; lean_object* v_lower_1923_; lean_object* v_upper_1924_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_numParams_1921_ = lean_ctor_get(v___x_1917_, 1);
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = lean_array_get_size(v_a_1920_);
v___x_2018_ = lean_nat_dec_le(v_numParams_1921_, v___x_2016_);
if (v___x_2018_ == 0)
{
lean_inc(v_numParams_1921_);
v_lower_1923_ = v_numParams_1921_;
v_upper_1924_ = v___x_2017_;
goto v___jp_1922_;
}
else
{
v_lower_1923_ = v___x_2016_;
v_upper_1924_ = v___x_2017_;
goto v___jp_1922_;
}
v___jp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = l_Array_toSubarray___redArg(v_a_1920_, v_lower_1923_, v_upper_1924_);
lean_inc_ref(v___x_1925_);
v___x_1926_ = l_Subarray_copy___redArg(v___x_1925_);
v___x_1927_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_1926_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1921_);
lean_inc_ref(v_argNames_1902_);
v___x_1930_ = l_Array_toSubarray___redArg(v_argNames_1902_, v___x_1929_, v_numParams_1921_);
v___x_1931_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_1932_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1930_, v___x_1931_);
v___x_1933_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v___x_1925_, v___x_1931_);
v_a_1934_ = l_Array_append___redArg(v___x_1932_, v___x_1933_);
lean_dec_ref(v___x_1933_);
v___x_1935_ = lean_array_get_size(v_a_1934_);
v___x_1936_ = l_Array_toSubarray___redArg(v_a_1934_, v___x_1929_, v___x_1935_);
v___x_1937_ = l_Subarray_copy___redArg(v___x_1936_);
lean_inc(v___x_1917_);
v___x_1938_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_1917_, v___x_1937_, v___y_1910_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_ref_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_ref_1940_ = lean_ctor_get(v___y_1910_, 2);
v___x_1941_ = 0;
v___x_1942_ = l_Lean_SourceInfo_fromRef(v_ref_1940_, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_1903_);
v___x_1944_ = l_Lean_mkCIdent(v_className_1903_);
v___x_1945_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_1942_);
v___x_1946_ = l_Lean_Syntax_node1(v___x_1942_, v___x_1945_, v_a_1939_);
v___x_1947_ = l_Lean_Syntax_node2(v___x_1942_, v___x_1943_, v___x_1944_, v___x_1946_);
v___x_1948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc_n(v_a_1949_, 4);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1));
v___x_1951_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_1952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1949_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
lean_inc(v___x_1918_);
v___x_1953_ = l_Lean_mkIdent(v___x_1918_);
v___x_1954_ = l_Lean_Syntax_node1(v_a_1949_, v___x_1945_, v___x_1953_);
v___x_1955_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_1956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1949_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_Syntax_node3(v_a_1949_, v___x_1950_, v___x_1952_, v___x_1954_, v___x_1956_);
v___x_1958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__5));
v___x_1959_ = l_Lean_Core_mkFreshUserName(v___x_1958_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc_n(v_a_1962_, 8);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__7));
v___x_1964_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__9));
v___x_1965_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__11));
v___x_1966_ = l_Lean_mkIdent(v_a_1960_);
v___x_1967_ = l_Lean_Syntax_node1(v_a_1962_, v___x_1965_, v___x_1966_);
v___x_1968_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_1969_ = l_Array_append___redArg(v___x_1968_, v_a_1928_);
lean_dec(v_a_1928_);
v___x_1970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1970_, 0, v_a_1962_);
lean_ctor_set(v___x_1970_, 1, v___x_1945_);
lean_ctor_set(v___x_1970_, 2, v___x_1969_);
v___x_1971_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__13));
v___x_1972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_1973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_a_1962_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_Syntax_node2(v_a_1962_, v___x_1971_, v___x_1973_, v___x_1947_);
v___x_1975_ = l_Lean_Syntax_node1(v_a_1962_, v___x_1945_, v___x_1974_);
v___x_1976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_1977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1962_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_Syntax_node5(v_a_1962_, v___x_1964_, v___x_1967_, v___x_1970_, v___x_1975_, v___x_1977_, v___x_1957_);
v___x_1979_ = l_Lean_Syntax_node1(v_a_1962_, v___x_1963_, v___x_1978_);
v___x_1980_ = lean_array_push(v_b_1905_, v___x_1979_);
v___x_1981_ = lean_unsigned_to_nat(1u);
v___x_1982_ = lean_nat_add(v_a_1904_, v___x_1981_);
lean_dec(v_a_1904_);
v_a_1904_ = v___x_1982_;
v_b_1905_ = v___x_1980_;
goto _start;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_a_1960_);
lean_dec(v___x_1957_);
lean_dec(v___x_1947_);
lean_dec(v_a_1928_);
lean_dec_ref(v_b_1905_);
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
v_a_1984_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1961_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1961_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v___x_1957_);
lean_dec(v___x_1947_);
lean_dec(v_a_1928_);
lean_dec_ref(v_b_1905_);
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
v_a_1992_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1959_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1959_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v___x_1947_);
lean_dec(v_a_1928_);
lean_dec_ref(v_b_1905_);
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
v_a_2000_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1948_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1948_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1928_);
lean_dec_ref(v_b_1905_);
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
v_a_2008_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1938_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1938_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_dec_ref(v___x_1925_);
lean_dec_ref(v_b_1905_);
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_b_1905_);
lean_dec(v_a_1904_);
lean_dec(v_className_1903_);
lean_dec_ref(v_argNames_1902_);
v_a_2019_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1919_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1919_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1899_ = stack[0].m_obj;
lean_object* v___x_1900_ = stack[1].m_obj;
lean_object* v_ctx_1901_ = stack[2].m_obj;
lean_object* v_argNames_1902_ = stack[3].m_obj;
lean_object* v_className_1903_ = stack[4].m_obj;
lean_object* v_a_1904_ = stack[5].m_obj;
lean_object* v_b_1905_ = stack[6].m_obj;
lean_object* v___y_1906_ = stack[7].m_obj;
lean_object* v___y_1907_ = stack[8].m_obj;
lean_object* v___y_1908_ = stack[9].m_obj;
lean_object* v___y_1909_ = stack[10].m_obj;
lean_object* v___y_1910_ = stack[11].m_obj;
lean_object* v___y_1911_ = stack[12].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_1899_, v___x_1900_, v_ctx_1901_, v_argNames_1902_, v_className_1903_, v_a_1904_, v_b_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___boxed(lean_object* v_upperBound_2028_, lean_object* v___x_2029_, lean_object* v_ctx_2030_, lean_object* v_argNames_2031_, lean_object* v_className_2032_, lean_object* v_a_2033_, lean_object* v_b_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_2028_, v___x_2029_, v_ctx_2030_, v_argNames_2031_, v_className_2032_, v_a_2033_, v_b_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec_ref(v_ctx_2030_);
lean_dec_ref(v___x_2029_);
lean_dec(v_upperBound_2028_);
return v_res_2042_;
}
}
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object* v_ctx_2043_, lean_object* v_className_2044_, lean_object* v_argNames_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_typeInfos_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v_letDecls_2056_; lean_object* v___x_2057_; 
v_typeInfos_2053_ = lean_ctor_get(v_ctx_2043_, 1);
v___x_2054_ = lean_array_get_size(v_typeInfos_2053_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v_letDecls_2056_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2057_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v___x_2054_, v_typeInfos_2053_, v_ctx_2043_, v_argNames_2045_, v_className_2044_, v___x_2055_, v_letDecls_2056_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2057_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkLocalInstanceLetDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2043_ = stack[0].m_obj;
lean_object* v_className_2044_ = stack[1].m_obj;
lean_object* v_argNames_2045_ = stack[2].m_obj;
lean_object* v_a_2046_ = stack[3].m_obj;
lean_object* v_a_2047_ = stack[4].m_obj;
lean_object* v_a_2048_ = stack[5].m_obj;
lean_object* v_a_2049_ = stack[6].m_obj;
lean_object* v_a_2050_ = stack[7].m_obj;
lean_object* v_a_2051_ = stack[8].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2043_, v_className_2044_, v_argNames_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2059_, lean_object* v_className_2060_, lean_object* v_argNames_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2059_, v_className_2060_, v_argNames_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec_ref(v_ctx_2059_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2070_, lean_object* v_R_2071_, lean_object* v_a_2072_, lean_object* v_b_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2072_, v_b_2073_);
return v___x_2074_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(lean_object* v_upperBound_2075_, lean_object* v___x_2076_, lean_object* v_ctx_2077_, lean_object* v_argNames_2078_, lean_object* v_className_2079_, lean_object* v_inst_2080_, lean_object* v_R_2081_, lean_object* v_a_2082_, lean_object* v_b_2083_, lean_object* v_c_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg(v_upperBound_2075_, v___x_2076_, v_ctx_2077_, v_argNames_2078_, v_className_2079_, v_a_2082_, v_b_2083_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2075_ = stack[0].m_obj;
lean_object* v___x_2076_ = stack[1].m_obj;
lean_object* v_ctx_2077_ = stack[2].m_obj;
lean_object* v_argNames_2078_ = stack[3].m_obj;
lean_object* v_className_2079_ = stack[4].m_obj;
lean_object* v_a_2082_ = stack[7].m_obj;
lean_object* v_b_2083_ = stack[8].m_obj;
lean_object* v___y_2085_ = stack[10].m_obj;
lean_object* v___y_2086_ = stack[11].m_obj;
lean_object* v___y_2087_ = stack[12].m_obj;
lean_object* v___y_2088_ = stack[13].m_obj;
lean_object* v___y_2089_ = stack[14].m_obj;
lean_object* v___y_2090_ = stack[15].m_obj;
lean_object* v_res_2093_;
v_res_2093_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(v_upperBound_2075_, v___x_2076_, v_ctx_2077_, v_argNames_2078_, v_className_2079_, lean_box(0), lean_box(0), v_a_2082_, v_b_2083_, lean_box(0), v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
stack->m_obj
 = v_res_2093_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2094_ = _args[0];
lean_object* v___x_2095_ = _args[1];
lean_object* v_ctx_2096_ = _args[2];
lean_object* v_argNames_2097_ = _args[3];
lean_object* v_className_2098_ = _args[4];
lean_object* v_inst_2099_ = _args[5];
lean_object* v_R_2100_ = _args[6];
lean_object* v_a_2101_ = _args[7];
lean_object* v_b_2102_ = _args[8];
lean_object* v_c_2103_ = _args[9];
lean_object* v___y_2104_ = _args[10];
lean_object* v___y_2105_ = _args[11];
lean_object* v___y_2106_ = _args[12];
lean_object* v___y_2107_ = _args[13];
lean_object* v___y_2108_ = _args[14];
lean_object* v___y_2109_ = _args[15];
lean_object* v___y_2110_ = _args[16];
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1(v_upperBound_2094_, v___x_2095_, v_ctx_2096_, v_argNames_2097_, v_className_2098_, v_inst_2099_, v_R_2100_, v_a_2101_, v_b_2102_, v_c_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v_ctx_2096_);
lean_dec_ref(v___x_2095_);
lean_dec(v_upperBound_2094_);
return v_res_2111_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(lean_object* v_as_2125_, size_t v_i_2126_, size_t v_stop_2127_, lean_object* v_b_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_eq(v_i_2126_, v_stop_2127_);
if (v___x_2131_ == 0)
{
lean_object* v_ref_2132_; size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_ref_2132_ = lean_ctor_get(v___y_2129_, 2);
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_sub(v_i_2126_, v___x_2133_);
v___x_2135_ = lean_array_uget_borrowed(v_as_2125_, v___x_2134_);
v___x_2136_ = l_Lean_SourceInfo_fromRef(v_ref_2132_, v___x_2131_);
v___x_2137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__0));
v___x_2138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__1));
lean_inc_n(v___x_2136_, 4);
v___x_2139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2136_);
lean_ctor_set(v___x_2139_, 1, v___x_2137_);
v___x_2140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__3));
v___x_2141_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2142_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2136_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
lean_ctor_set(v___x_2143_, 2, v___x_2142_);
v___x_2144_ = l_Lean_Syntax_node1(v___x_2136_, v___x_2140_, v___x_2143_);
v___x_2145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___closed__4));
v___x_2146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2136_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
lean_inc(v___x_2135_);
v___x_2147_ = l_Lean_Syntax_node5(v___x_2136_, v___x_2138_, v___x_2139_, v___x_2144_, v___x_2135_, v___x_2146_, v_b_2128_);
v_i_2126_ = v___x_2134_;
v_b_2128_ = v___x_2147_;
goto _start;
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_b_2128_);
return v___x_2149_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2125_ = stack[0].m_obj;
size_t v_i_2126_ = stack[1].m_num;
size_t v_stop_2127_ = stack[2].m_num;
lean_object* v_b_2128_ = stack[3].m_obj;
lean_object* v___y_2129_ = stack[4].m_obj;
lean_object* v_res_2150_;
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2125_, v_i_2126_, v_stop_2127_, v_b_2128_, v___y_2129_);
stack->m_obj
 = v_res_2150_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg___boxed(lean_object* v_as_2151_, lean_object* v_i_2152_, lean_object* v_stop_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
size_t v_i_boxed_2157_; size_t v_stop_boxed_2158_; lean_object* v_res_2159_; 
v_i_boxed_2157_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_stop_boxed_2158_ = lean_unbox_usize(v_stop_2153_);
lean_dec(v_stop_2153_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2151_, v_i_boxed_2157_, v_stop_boxed_2158_, v_b_2154_, v___y_2155_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v_as_2151_);
return v_res_2159_;
}
}
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object* v_letDecls_2160_, lean_object* v_body_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2169_ = lean_array_get_size(v_letDecls_2160_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_nat_dec_lt(v___x_2170_, v___x_2169_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_body_2161_);
return v___x_2172_;
}
else
{
size_t v___x_2173_; size_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_usize_of_nat(v___x_2169_);
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_letDecls_2160_, v___x_2173_, v___x_2174_, v_body_2161_, v_a_2166_);
return v___x_2175_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_letDecls_2160_ = stack[0].m_obj;
lean_object* v_body_2161_ = stack[1].m_obj;
lean_object* v_a_2162_ = stack[2].m_obj;
lean_object* v_a_2163_ = stack[3].m_obj;
lean_object* v_a_2164_ = stack[4].m_obj;
lean_object* v_a_2165_ = stack[5].m_obj;
lean_object* v_a_2166_ = stack[6].m_obj;
lean_object* v_a_2167_ = stack[7].m_obj;
lean_object* v_res_2176_;
v_res_2176_ = l_Lean_Elab_Deriving_mkLet(v_letDecls_2160_, v_body_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
stack->m_obj
 = v_res_2176_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkLet___boxed(lean_object* v_letDecls_2177_, lean_object* v_body_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Elab_Deriving_mkLet(v_letDecls_2177_, v_body_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec_ref(v_letDecls_2177_);
return v_res_2186_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(lean_object* v_as_2187_, size_t v_i_2188_, size_t v_stop_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___redArg(v_as_2187_, v_i_2188_, v_stop_2189_, v_b_2190_, v___y_2195_);
return v___x_2198_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2187_ = stack[0].m_obj;
size_t v_i_2188_ = stack[1].m_num;
size_t v_stop_2189_ = stack[2].m_num;
lean_object* v_b_2190_ = stack[3].m_obj;
lean_object* v___y_2191_ = stack[4].m_obj;
lean_object* v___y_2192_ = stack[5].m_obj;
lean_object* v___y_2193_ = stack[6].m_obj;
lean_object* v___y_2194_ = stack[7].m_obj;
lean_object* v___y_2195_ = stack[8].m_obj;
lean_object* v___y_2196_ = stack[9].m_obj;
lean_object* v_res_2199_;
v_res_2199_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_2187_, v_i_2188_, v_stop_2189_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
stack->m_obj
 = v_res_2199_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0___boxed(lean_object* v_as_2200_, lean_object* v_i_2201_, lean_object* v_stop_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
size_t v_i_boxed_2211_; size_t v_stop_boxed_2212_; lean_object* v_res_2213_; 
v_i_boxed_2211_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_stop_boxed_2212_ = lean_unbox_usize(v_stop_2202_);
lean_dec(v_stop_2202_);
v_res_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Deriving_mkLet_spec__0(v_as_2200_, v_i_boxed_2211_, v_stop_boxed_2212_, v_b_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_as_2200_);
return v_res_2213_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(lean_object* v___f_2223_, lean_object* v___x_2224_, lean_object* v___x_2225_, lean_object* v___x_2226_, lean_object* v___x_2227_, lean_object* v_instName_2228_, lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v_b_2231_, lean_object* v_____r_2232_, lean_object* v_val_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
v___x_2241_ = lean_apply_7(v___f_2223_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, lean_box(0));
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2291_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2291_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2291_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2246_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__0));
v___x_2247_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__1));
lean_inc_ref_n(v___x_2225_, 8);
lean_inc_ref_n(v___x_2224_, 8);
v___x_2248_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2246_, v___x_2247_);
v___x_2249_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__2));
v___x_2250_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2246_, v___x_2249_);
v___x_2251_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc_n(v___x_2226_, 2);
lean_inc_n(v_a_2242_, 14);
v___x_2252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2252_, 0, v_a_2242_);
lean_ctor_set(v___x_2252_, 1, v___x_2226_);
lean_ctor_set(v___x_2252_, 2, v___x_2251_);
lean_inc_ref_n(v___x_2252_, 12);
v___x_2253_ = l_Lean_Syntax_node7(v_a_2242_, v___x_2250_, v___x_2252_, v___x_2252_, v___x_2252_, v___x_2252_, v___x_2252_, v___x_2252_, v___x_2252_);
v___x_2254_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__3));
v___x_2255_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2246_, v___x_2254_);
v___x_2256_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Elab_Deriving_withoutExposeFromCtors_spec__4___closed__2));
lean_inc_ref(v___x_2227_);
v___x_2257_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2227_, v___x_2256_);
v___x_2258_ = l_Lean_Syntax_node1(v_a_2242_, v___x_2257_, v___x_2252_);
v___x_2259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_a_2242_);
lean_ctor_set(v___x_2259_, 1, v___x_2254_);
v___x_2260_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__4));
v___x_2261_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2246_, v___x_2260_);
v___x_2262_ = l_Lean_mkIdent(v_instName_2228_);
v___x_2263_ = l_Lean_Syntax_node2(v_a_2242_, v___x_2261_, v___x_2262_, v___x_2252_);
v___x_2264_ = l_Lean_Syntax_node1(v_a_2242_, v___x_2226_, v___x_2263_);
v___x_2265_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__5));
v___x_2266_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2246_, v___x_2265_);
v___x_2267_ = l_Array_append___redArg(v___x_2251_, v___x_2229_);
v___x_2268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2268_, 0, v_a_2242_);
lean_ctor_set(v___x_2268_, 1, v___x_2226_);
lean_ctor_set(v___x_2268_, 2, v___x_2267_);
v___x_2269_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__12));
v___x_2270_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2227_, v___x_2269_);
v___x_2271_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2242_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l_Lean_Syntax_node2(v_a_2242_, v___x_2270_, v___x_2272_, v___x_2230_);
v___x_2274_ = l_Lean_Syntax_node2(v_a_2242_, v___x_2266_, v___x_2268_, v___x_2273_);
v___x_2275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__6));
v___x_2276_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2246_, v___x_2275_);
v___x_2277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__15));
v___x_2278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_a_2242_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__7));
v___x_2280_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___closed__8));
v___x_2281_ = l_Lean_Name_mkStr4(v___x_2224_, v___x_2225_, v___x_2279_, v___x_2280_);
v___x_2282_ = l_Lean_Syntax_node2(v_a_2242_, v___x_2281_, v___x_2252_, v___x_2252_);
v___x_2283_ = l_Lean_Syntax_node4(v_a_2242_, v___x_2276_, v___x_2278_, v_val_2233_, v___x_2282_, v___x_2252_);
v___x_2284_ = l_Lean_Syntax_node6(v_a_2242_, v___x_2255_, v___x_2258_, v___x_2259_, v___x_2252_, v___x_2264_, v___x_2274_, v___x_2283_);
v___x_2285_ = l_Lean_Syntax_node2(v_a_2242_, v___x_2248_, v___x_2253_, v___x_2284_);
v___x_2286_ = lean_array_push(v_b_2231_, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2287_);
v___x_2289_ = v___x_2244_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_val_2233_);
lean_dec_ref(v_b_2231_);
lean_dec(v___x_2230_);
lean_dec(v_instName_2228_);
lean_dec_ref(v___x_2227_);
lean_dec(v___x_2226_);
lean_dec_ref(v___x_2225_);
lean_dec_ref(v___x_2224_);
v_a_2292_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2241_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2241_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2223_ = stack[0].m_obj;
lean_object* v___x_2224_ = stack[1].m_obj;
lean_object* v___x_2225_ = stack[2].m_obj;
lean_object* v___x_2226_ = stack[3].m_obj;
lean_object* v___x_2227_ = stack[4].m_obj;
lean_object* v_instName_2228_ = stack[5].m_obj;
lean_object* v___x_2229_ = stack[6].m_obj;
lean_object* v___x_2230_ = stack[7].m_obj;
lean_object* v_b_2231_ = stack[8].m_obj;
lean_object* v_____r_2232_ = stack[9].m_obj;
lean_object* v_val_2233_ = stack[10].m_obj;
lean_object* v___y_2234_ = stack[11].m_obj;
lean_object* v___y_2235_ = stack[12].m_obj;
lean_object* v___y_2236_ = stack[13].m_obj;
lean_object* v___y_2237_ = stack[14].m_obj;
lean_object* v___y_2238_ = stack[15].m_obj;
lean_object* v___y_2239_ = stack[16].m_obj;
lean_object* v_res_2300_;
v_res_2300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2223_, v___x_2224_, v___x_2225_, v___x_2226_, v___x_2227_, v_instName_2228_, v___x_2229_, v___x_2230_, v_b_2231_, v_____r_2232_, v_val_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
stack->m_obj
 = v_res_2300_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___f_2301_ = _args[0];
lean_object* v___x_2302_ = _args[1];
lean_object* v___x_2303_ = _args[2];
lean_object* v___x_2304_ = _args[3];
lean_object* v___x_2305_ = _args[4];
lean_object* v_instName_2306_ = _args[5];
lean_object* v___x_2307_ = _args[6];
lean_object* v___x_2308_ = _args[7];
lean_object* v_b_2309_ = _args[8];
lean_object* v_____r_2310_ = _args[9];
lean_object* v_val_2311_ = _args[10];
lean_object* v___y_2312_ = _args[11];
lean_object* v___y_2313_ = _args[12];
lean_object* v___y_2314_ = _args[13];
lean_object* v___y_2315_ = _args[14];
lean_object* v___y_2316_ = _args[15];
lean_object* v___y_2317_ = _args[16];
lean_object* v___y_2318_ = _args[17];
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2301_, v___x_2302_, v___x_2303_, v___x_2304_, v___x_2305_, v_instName_2306_, v___x_2307_, v___x_2308_, v_b_2309_, v_____r_2310_, v_val_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___x_2307_);
return v_res_2319_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_2320_, lean_object* v_as_2321_, size_t v_i_2322_, size_t v_stop_2323_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_eq(v_i_2322_, v_stop_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = lean_array_uget_borrowed(v_as_2321_, v_i_2322_);
v___x_2326_ = lean_name_eq(v_a_2320_, v___x_2325_);
if (v___x_2326_ == 0)
{
size_t v___x_2327_; size_t v___x_2328_; 
v___x_2327_ = ((size_t)1ULL);
v___x_2328_ = lean_usize_add(v_i_2322_, v___x_2327_);
v_i_2322_ = v___x_2328_;
goto _start;
}
else
{
return v___x_2326_;
}
}
else
{
uint8_t v___x_2330_; 
v___x_2330_ = 0;
return v___x_2330_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2320_ = stack[0].m_obj;
lean_object* v_as_2321_ = stack[1].m_obj;
size_t v_i_2322_ = stack[2].m_num;
size_t v_stop_2323_ = stack[3].m_num;
uint8_t v_res_2331_;
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2320_, v_as_2321_, v_i_2322_, v_stop_2323_);
stack->m_num = v_res_2331_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_2332_, lean_object* v_as_2333_, lean_object* v_i_2334_, lean_object* v_stop_2335_){
_start:
{
size_t v_i_boxed_2336_; size_t v_stop_boxed_2337_; uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_i_boxed_2336_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_stop_boxed_2337_ = lean_unbox_usize(v_stop_2335_);
lean_dec(v_stop_2335_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2332_, v_as_2333_, v_i_boxed_2336_, v_stop_boxed_2337_);
lean_dec_ref(v_as_2333_);
lean_dec(v_a_2332_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
uint8_t l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(lean_object* v_as_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_array_get_size(v_as_2340_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
size_t v___x_2345_; size_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = lean_usize_of_nat(v___x_2343_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_spec__0(v_a_2341_, v_as_2340_, v___x_2345_, v___x_2346_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2340_ = stack[0].m_obj;
lean_object* v_a_2341_ = stack[1].m_obj;
uint8_t v_res_2348_;
v_res_2348_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_2340_, v_a_2341_);
stack->m_num = v_res_2348_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0___boxed(lean_object* v_as_2349_, lean_object* v_a_2350_){
_start:
{
uint8_t v_res_2351_; lean_object* v_r_2352_; 
v_res_2351_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_as_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_as_2349_);
v_r_2352_ = lean_box(v_res_2351_);
return v_r_2352_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(lean_object* v_upperBound_2354_, lean_object* v___x_2355_, lean_object* v_typeNames_2356_, lean_object* v_ctx_2357_, lean_object* v_className_2358_, uint8_t v_useAnonCtor_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_a_2370_; lean_object* v___y_2375_; uint8_t v___x_2394_; 
v___x_2394_ = lean_nat_dec_lt(v_a_2360_, v_upperBound_2354_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v_b_2361_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v_toConstantVal_2398_; lean_object* v_name_2399_; uint8_t v___x_2400_; 
v___x_2396_ = l_Lean_instInhabitedInductiveVal_default;
v___x_2397_ = lean_array_get_borrowed(v___x_2396_, v___x_2355_, v_a_2360_);
v_toConstantVal_2398_ = lean_ctor_get(v___x_2397_, 0);
v_name_2399_ = lean_ctor_get(v_toConstantVal_2398_, 0);
v___x_2400_ = l_Array_contains___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__0(v_typeNames_2356_, v_name_2399_);
if (v___x_2400_ == 0)
{
v_a_2370_ = v_b_2361_;
goto v___jp_2369_;
}
else
{
lean_object* v_instName_2401_; lean_object* v_auxFunNames_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_instName_2401_ = lean_ctor_get(v_ctx_2357_, 0);
v_auxFunNames_2402_ = lean_ctor_get(v_ctx_2357_, 2);
v___f_2403_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___closed__0));
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_array_get_borrowed(v___x_2404_, v_auxFunNames_2402_, v_a_2360_);
lean_inc(v___x_2397_);
v___x_2406_ = l_Lean_Elab_Deriving_mkInductArgNames(v___x_2397_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc_n(v_a_2407_, 2);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2407_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
lean_inc(v_a_2407_);
lean_inc(v___x_2397_);
lean_inc(v_className_2358_);
v___x_2410_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2358_, v___x_2397_, v_a_2407_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v___x_2412_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__0));
v___x_2413_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__1));
v___x_2414_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__2));
v___x_2415_ = l_Array_append___redArg(v_a_2409_, v_a_2411_);
lean_dec(v_a_2411_);
lean_inc(v___x_2397_);
v___x_2416_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v___x_2397_, v_a_2407_, v___y_2366_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v_ref_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v_ref_2418_ = lean_ctor_get(v___y_2366_, 2);
v___x_2419_ = 0;
v___x_2420_ = l_Lean_SourceInfo_fromRef(v_ref_2418_, v___x_2419_);
v___x_2421_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__4));
lean_inc(v_className_2358_);
v___x_2422_ = l_Lean_mkCIdent(v_className_2358_);
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
lean_inc(v___x_2420_);
v___x_2424_ = l_Lean_Syntax_node1(v___x_2420_, v___x_2423_, v_a_2417_);
v___x_2425_ = l_Lean_Syntax_node2(v___x_2420_, v___x_2421_, v___x_2422_, v___x_2424_);
lean_inc(v___x_2405_);
v___x_2426_ = l_Lean_mkIdent(v___x_2405_);
if (v_useAnonCtor_2359_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_box(0);
lean_inc(v_instName_2401_);
v___x_2428_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2403_, v___x_2412_, v___x_2413_, v___x_2423_, v___x_2414_, v_instName_2401_, v___x_2415_, v___x_2425_, v_b_2361_, v___x_2427_, v___x_2426_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v___x_2415_);
v___y_2375_ = v___x_2428_;
goto v___jp_2374_;
}
else
{
lean_object* v___x_2429_; 
v___x_2429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___lam__0(v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_n(v_a_2430_, 4);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__1));
v___x_2432_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__2));
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2430_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = l_Lean_Syntax_node1(v_a_2430_, v___x_2423_, v___x_2426_);
v___x_2435_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__3));
v___x_2436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2430_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_Syntax_node3(v_a_2430_, v___x_2431_, v___x_2433_, v___x_2434_, v___x_2436_);
v___x_2438_ = lean_box(0);
lean_inc(v_instName_2401_);
v___x_2439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___lam__1(v___f_2403_, v___x_2412_, v___x_2413_, v___x_2423_, v___x_2414_, v_instName_2401_, v___x_2415_, v___x_2425_, v_b_2361_, v___x_2438_, v___x_2437_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v___x_2415_);
v___y_2375_ = v___x_2439_;
goto v___jp_2374_;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v___x_2426_);
lean_dec(v___x_2425_);
lean_dec_ref(v___x_2415_);
lean_dec_ref(v_b_2361_);
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v_a_2440_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2429_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2429_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec_ref(v___x_2415_);
lean_dec_ref(v_b_2361_);
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v_a_2448_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2416_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2416_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2409_);
lean_dec(v_a_2407_);
lean_dec_ref(v_b_2361_);
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v_a_2456_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2410_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2410_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_dec(v_a_2407_);
lean_dec_ref(v_b_2361_);
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
return v___x_2408_;
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_b_2361_);
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v_a_2464_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2406_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2406_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
v___jp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = lean_nat_add(v_a_2360_, v___x_2371_);
lean_dec(v_a_2360_);
v_a_2360_ = v___x_2372_;
v_b_2361_ = v_a_2370_;
goto _start;
}
v___jp_2374_:
{
if (lean_obj_tag(v___y_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2385_; 
v_a_2376_ = lean_ctor_get(v___y_2375_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___y_2375_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2378_ = v___y_2375_;
v_isShared_2379_ = v_isSharedCheck_2385_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___y_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2385_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
if (lean_obj_tag(v_a_2376_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; 
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v_a_2380_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v_a_2376_, 1);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v_a_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
else
{
lean_object* v_a_2384_; 
lean_del_object(v___x_2378_);
v_a_2384_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v_a_2376_, 1);
v_a_2370_ = v_a_2384_;
goto v___jp_2369_;
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_a_2360_);
lean_dec(v_className_2358_);
lean_dec_ref(v_ctx_2357_);
v_a_2386_ = lean_ctor_get(v___y_2375_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___y_2375_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___y_2375_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___y_2375_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2354_ = stack[0].m_obj;
lean_object* v___x_2355_ = stack[1].m_obj;
lean_object* v_typeNames_2356_ = stack[2].m_obj;
lean_object* v_ctx_2357_ = stack[3].m_obj;
lean_object* v_className_2358_ = stack[4].m_obj;
uint8_t v_useAnonCtor_2359_ = stack[5].m_num;
lean_object* v_a_2360_ = stack[6].m_obj;
lean_object* v_b_2361_ = stack[7].m_obj;
lean_object* v___y_2362_ = stack[8].m_obj;
lean_object* v___y_2363_ = stack[9].m_obj;
lean_object* v___y_2364_ = stack[10].m_obj;
lean_object* v___y_2365_ = stack[11].m_obj;
lean_object* v___y_2366_ = stack[12].m_obj;
lean_object* v___y_2367_ = stack[13].m_obj;
lean_object* v_res_2472_;
v_res_2472_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2354_, v___x_2355_, v_typeNames_2356_, v_ctx_2357_, v_className_2358_, v_useAnonCtor_2359_, v_a_2360_, v_b_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
stack->m_obj
 = v_res_2472_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_upperBound_2473_, lean_object* v___x_2474_, lean_object* v_typeNames_2475_, lean_object* v_ctx_2476_, lean_object* v_className_2477_, lean_object* v_useAnonCtor_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v_useAnonCtor_boxed_2488_; lean_object* v_res_2489_; 
v_useAnonCtor_boxed_2488_ = lean_unbox(v_useAnonCtor_2478_);
v_res_2489_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2473_, v___x_2474_, v_typeNames_2475_, v_ctx_2476_, v_className_2477_, v_useAnonCtor_boxed_2488_, v_a_2479_, v_b_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v_typeNames_2475_);
lean_dec_ref(v___x_2474_);
lean_dec(v_upperBound_2473_);
return v_res_2489_;
}
}
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object* v_ctx_2490_, lean_object* v_className_2491_, lean_object* v_typeNames_2492_, uint8_t v_useAnonCtor_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_typeInfos_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v_instances_2504_; lean_object* v___x_2505_; 
v_typeInfos_2501_ = lean_ctor_get(v_ctx_2490_, 1);
lean_inc_ref(v_typeInfos_2501_);
v___x_2502_ = lean_array_get_size(v_typeInfos_2501_);
v___x_2503_ = lean_unsigned_to_nat(0u);
v_instances_2504_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v___x_2502_, v_typeInfos_2501_, v_typeNames_2492_, v_ctx_2490_, v_className_2491_, v_useAnonCtor_2493_, v___x_2503_, v_instances_2504_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec_ref(v_typeInfos_2501_);
return v___x_2505_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkInstanceCmds_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2490_ = stack[0].m_obj;
lean_object* v_className_2491_ = stack[1].m_obj;
lean_object* v_typeNames_2492_ = stack[2].m_obj;
uint8_t v_useAnonCtor_2493_ = stack[3].m_num;
lean_object* v_a_2494_ = stack[4].m_obj;
lean_object* v_a_2495_ = stack[5].m_obj;
lean_object* v_a_2496_ = stack[6].m_obj;
lean_object* v_a_2497_ = stack[7].m_obj;
lean_object* v_a_2498_ = stack[8].m_obj;
lean_object* v_a_2499_ = stack[9].m_obj;
lean_object* v_res_2506_;
v_res_2506_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_2490_, v_className_2491_, v_typeNames_2492_, v_useAnonCtor_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
stack->m_obj
 = v_res_2506_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInstanceCmds___boxed(lean_object* v_ctx_2507_, lean_object* v_className_2508_, lean_object* v_typeNames_2509_, lean_object* v_useAnonCtor_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
uint8_t v_useAnonCtor_boxed_2518_; lean_object* v_res_2519_; 
v_useAnonCtor_boxed_2518_ = lean_unbox(v_useAnonCtor_2510_);
v_res_2519_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_ctx_2507_, v_className_2508_, v_typeNames_2509_, v_useAnonCtor_boxed_2518_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_typeNames_2509_);
return v_res_2519_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(lean_object* v_upperBound_2520_, lean_object* v___x_2521_, lean_object* v_typeNames_2522_, lean_object* v_ctx_2523_, lean_object* v_className_2524_, uint8_t v_useAnonCtor_2525_, lean_object* v_inst_2526_, lean_object* v_R_2527_, lean_object* v_a_2528_, lean_object* v_b_2529_, lean_object* v_c_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___redArg(v_upperBound_2520_, v___x_2521_, v_typeNames_2522_, v_ctx_2523_, v_className_2524_, v_useAnonCtor_2525_, v_a_2528_, v_b_2529_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
return v___x_2538_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2520_ = stack[0].m_obj;
lean_object* v___x_2521_ = stack[1].m_obj;
lean_object* v_typeNames_2522_ = stack[2].m_obj;
lean_object* v_ctx_2523_ = stack[3].m_obj;
lean_object* v_className_2524_ = stack[4].m_obj;
uint8_t v_useAnonCtor_2525_ = stack[5].m_num;
lean_object* v_a_2528_ = stack[8].m_obj;
lean_object* v_b_2529_ = stack[9].m_obj;
lean_object* v___y_2531_ = stack[11].m_obj;
lean_object* v___y_2532_ = stack[12].m_obj;
lean_object* v___y_2533_ = stack[13].m_obj;
lean_object* v___y_2534_ = stack[14].m_obj;
lean_object* v___y_2535_ = stack[15].m_obj;
lean_object* v___y_2536_ = stack[16].m_obj;
lean_object* v_res_2539_;
v_res_2539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(v_upperBound_2520_, v___x_2521_, v_typeNames_2522_, v_ctx_2523_, v_className_2524_, v_useAnonCtor_2525_, lean_box(0), lean_box(0), v_a_2528_, v_b_2529_, lean_box(0), v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
stack->m_obj
 = v_res_2539_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2540_ = _args[0];
lean_object* v___x_2541_ = _args[1];
lean_object* v_typeNames_2542_ = _args[2];
lean_object* v_ctx_2543_ = _args[3];
lean_object* v_className_2544_ = _args[4];
lean_object* v_useAnonCtor_2545_ = _args[5];
lean_object* v_inst_2546_ = _args[6];
lean_object* v_R_2547_ = _args[7];
lean_object* v_a_2548_ = _args[8];
lean_object* v_b_2549_ = _args[9];
lean_object* v_c_2550_ = _args[10];
lean_object* v___y_2551_ = _args[11];
lean_object* v___y_2552_ = _args[12];
lean_object* v___y_2553_ = _args[13];
lean_object* v___y_2554_ = _args[14];
lean_object* v___y_2555_ = _args[15];
lean_object* v___y_2556_ = _args[16];
lean_object* v___y_2557_ = _args[17];
_start:
{
uint8_t v_useAnonCtor_boxed_2558_; lean_object* v_res_2559_; 
v_useAnonCtor_boxed_2558_ = lean_unbox(v_useAnonCtor_2545_);
v_res_2559_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkInstanceCmds_spec__1(v_upperBound_2540_, v___x_2541_, v_typeNames_2542_, v_ctx_2543_, v_className_2544_, v_useAnonCtor_boxed_2558_, v_inst_2546_, v_R_2547_, v_a_2548_, v_b_2549_, v_c_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v_typeNames_2542_);
lean_dec_ref(v___x_2541_);
lean_dec(v_upperBound_2540_);
return v_res_2559_;
}
}
lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg(lean_object* v_varName_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_ref_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_ref_2569_ = lean_ctor_get(v_a_2567_, 2);
v___x_2570_ = 0;
v___x_2571_ = l_Lean_SourceInfo_fromRef(v_ref_2569_, v___x_2570_);
v___x_2572_ = ((lean_object*)(l_Lean_Elab_Deriving_mkDiscr___redArg___closed__1));
v___x_2573_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2574_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
lean_inc(v___x_2571_);
v___x_2575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2571_);
lean_ctor_set(v___x_2575_, 1, v___x_2573_);
lean_ctor_set(v___x_2575_, 2, v___x_2574_);
v___x_2576_ = l_Lean_mkIdent(v_varName_2566_);
v___x_2577_ = l_Lean_Syntax_node2(v___x_2571_, v___x_2572_, v___x_2575_, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkDiscr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_varName_2566_ = stack[0].m_obj;
lean_object* v_a_2567_ = stack[1].m_obj;
lean_object* v_res_2579_;
v_res_2579_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2566_, v_a_2567_);
stack->m_obj
 = v_res_2579_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___redArg___boxed(lean_object* v_varName_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2580_, v_a_2581_);
lean_dec_ref(v_a_2581_);
return v_res_2583_;
}
}
lean_object* l_Lean_Elab_Deriving_mkDiscr(lean_object* v_varName_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_varName_2584_, v_a_2589_);
return v___x_2592_;
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkDiscr_0interp(lean_interpreter_value* stack)
{
lean_object* v_varName_2584_ = stack[0].m_obj;
lean_object* v_a_2585_ = stack[1].m_obj;
lean_object* v_a_2586_ = stack[2].m_obj;
lean_object* v_a_2587_ = stack[3].m_obj;
lean_object* v_a_2588_ = stack[4].m_obj;
lean_object* v_a_2589_ = stack[5].m_obj;
lean_object* v_a_2590_ = stack[6].m_obj;
lean_object* v_res_2593_;
v_res_2593_ = l_Lean_Elab_Deriving_mkDiscr(v_varName_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
stack->m_obj
 = v_res_2593_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscr___boxed(lean_object* v_varName_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Elab_Deriving_mkDiscr(v_varName_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
return v_res_2602_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(lean_object* v_upperBound_2606_, lean_object* v_a_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_nat_dec_lt(v_a_2607_, v_upperBound_2606_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec(v_a_2607_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_b_2608_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___closed__1));
v___x_2615_ = l_Lean_Core_mkFreshUserName(v___x_2614_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = lean_array_push(v_b_2608_, v_a_2616_);
v___x_2618_ = lean_unsigned_to_nat(1u);
v___x_2619_ = lean_nat_add(v_a_2607_, v___x_2618_);
lean_dec(v_a_2607_);
v_a_2607_ = v___x_2619_;
v_b_2608_ = v___x_2617_;
goto _start;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_b_2608_);
lean_dec(v_a_2607_);
v_a_2621_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2615_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2615_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2606_ = stack[0].m_obj;
lean_object* v_a_2607_ = stack[1].m_obj;
lean_object* v_b_2608_ = stack[2].m_obj;
lean_object* v___y_2609_ = stack[3].m_obj;
lean_object* v___y_2610_ = stack[4].m_obj;
lean_object* v_res_2629_;
v_res_2629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2606_, v_a_2607_, v_b_2608_, v___y_2609_, v___y_2610_);
stack->m_obj
 = v_res_2629_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg___boxed(lean_object* v_upperBound_2630_, lean_object* v_a_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2630_, v_a_2631_, v_b_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v_upperBound_2630_);
return v_res_2636_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(lean_object* v_a_2645_, size_t v_sz_2646_, size_t v_i_2647_, lean_object* v_bs_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_usize_dec_lt(v_i_2647_, v_sz_2646_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
lean_dec(v_a_2645_);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_bs_2648_);
return v___x_2652_;
}
else
{
lean_object* v_ref_2653_; lean_object* v_v_2654_; lean_object* v___x_2655_; lean_object* v_bs_x27_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v_ref_2653_ = lean_ctor_get(v___y_2649_, 2);
v_v_2654_ = lean_array_uget(v_bs_2648_, v_i_2647_);
v___x_2655_ = lean_unsigned_to_nat(0u);
v_bs_x27_2656_ = lean_array_uset(v_bs_2648_, v_i_2647_, v___x_2655_);
v___x_2657_ = 0;
v___x_2658_ = l_Lean_SourceInfo_fromRef(v_ref_2653_, v___x_2657_);
v___x_2659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__1));
v___x_2660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__2));
lean_inc_n(v___x_2658_, 6);
v___x_2661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2658_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__9));
v___x_2663_ = l_Lean_mkIdent(v_v_2654_);
v___x_2664_ = l_Lean_Syntax_node1(v___x_2658_, v___x_2662_, v___x_2663_);
v___x_2665_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkLocalInstanceLetDecls_spec__1___redArg___closed__14));
v___x_2666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2658_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
lean_inc(v_a_2645_);
v___x_2667_ = l_Lean_Syntax_node2(v___x_2658_, v___x_2662_, v___x_2666_, v_a_2645_);
v___x_2668_ = lean_obj_once(&l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10, &l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10_once, _init_l_Lean_Elab_Deriving_mkInductiveApp___redArg___closed__10);
v___x_2669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2658_);
lean_ctor_set(v___x_2669_, 1, v___x_2662_);
lean_ctor_set(v___x_2669_, 2, v___x_2668_);
v___x_2670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___closed__3));
v___x_2671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2658_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_Syntax_node5(v___x_2658_, v___x_2659_, v___x_2661_, v___x_2664_, v___x_2667_, v___x_2669_, v___x_2671_);
v___x_2673_ = ((size_t)1ULL);
v___x_2674_ = lean_usize_add(v_i_2647_, v___x_2673_);
v___x_2675_ = lean_array_uset(v_bs_x27_2656_, v_i_2647_, v___x_2672_);
v_i_2647_ = v___x_2674_;
v_bs_2648_ = v___x_2675_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2645_ = stack[0].m_obj;
size_t v_sz_2646_ = stack[1].m_num;
size_t v_i_2647_ = stack[2].m_num;
lean_object* v_bs_2648_ = stack[3].m_obj;
lean_object* v___y_2649_ = stack[4].m_obj;
lean_object* v_res_2677_;
v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2645_, v_sz_2646_, v_i_2647_, v_bs_2648_, v___y_2649_);
stack->m_obj
 = v_res_2677_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg___boxed(lean_object* v_a_2678_, lean_object* v_sz_2679_, lean_object* v_i_2680_, lean_object* v_bs_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
size_t v_sz_boxed_2684_; size_t v_i_boxed_2685_; lean_object* v_res_2686_; 
v_sz_boxed_2684_ = lean_unbox_usize(v_sz_2679_);
lean_dec(v_sz_2679_);
v_i_boxed_2685_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_res_2686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2678_, v_sz_boxed_2684_, v_i_boxed_2685_, v_bs_2681_, v___y_2682_);
lean_dec_ref(v___y_2682_);
return v_res_2686_;
}
}
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object* v_className_2687_, lean_object* v_arity_2688_, lean_object* v_indVal_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v___x_2697_; 
lean_inc_ref(v_indVal_2689_);
v___x_2697_ = l_Lean_Elab_Deriving_mkInductArgNames(v_indVal_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc_n(v_a_2698_, 2);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_2698_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
lean_inc(v_a_2698_);
lean_inc_ref(v_indVal_2689_);
v___x_2701_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indVal_2689_, v_a_2698_, v_a_2694_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInductArgNames___lam__0___closed__0));
v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_arity_2688_, v___x_2703_, v___x_2704_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
lean_inc(v_a_2698_);
v___x_2707_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v_className_2687_, v_indVal_2689_, v_a_2698_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2709_; size_t v_sz_2710_; size_t v___x_2711_; lean_object* v___x_2712_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = l_Array_append___redArg(v_a_2700_, v_a_2708_);
lean_dec(v_a_2708_);
v_sz_2710_ = lean_array_size(v_a_2706_);
v___x_2711_ = ((size_t)0ULL);
lean_inc(v_a_2706_);
lean_inc(v_a_2702_);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2702_, v_sz_2710_, v___x_2711_, v_a_2706_, v_a_2694_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2722_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2722_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2722_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2717_ = l_Array_append___redArg(v___x_2709_, v_a_2713_);
lean_dec(v_a_2713_);
v___x_2718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v_a_2698_);
lean_ctor_set(v___x_2718_, 2, v_a_2706_);
lean_ctor_set(v___x_2718_, 3, v_a_2702_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2718_);
v___x_2720_ = v___x_2715_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v___x_2709_);
lean_dec(v_a_2706_);
lean_dec(v_a_2702_);
lean_dec(v_a_2698_);
v_a_2723_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2712_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2712_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_a_2706_);
lean_dec(v_a_2702_);
lean_dec(v_a_2700_);
lean_dec(v_a_2698_);
v_a_2731_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2707_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2707_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2702_);
lean_dec(v_a_2700_);
lean_dec(v_a_2698_);
lean_dec_ref(v_indVal_2689_);
lean_dec(v_className_2687_);
v_a_2739_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2705_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2705_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2698_);
lean_dec_ref(v_indVal_2689_);
lean_dec(v_className_2687_);
v_a_2747_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2699_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2699_);
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
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_indVal_2689_);
lean_dec(v_className_2687_);
v_a_2755_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2697_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2697_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_className_2687_ = stack[0].m_obj;
lean_object* v_arity_2688_ = stack[1].m_obj;
lean_object* v_indVal_2689_ = stack[2].m_obj;
lean_object* v_a_2690_ = stack[3].m_obj;
lean_object* v_a_2691_ = stack[4].m_obj;
lean_object* v_a_2692_ = stack[5].m_obj;
lean_object* v_a_2693_ = stack[6].m_obj;
lean_object* v_a_2694_ = stack[7].m_obj;
lean_object* v_a_2695_ = stack[8].m_obj;
lean_object* v_res_2763_;
v_res_2763_ = l_Lean_Elab_Deriving_mkHeader(v_className_2687_, v_arity_2688_, v_indVal_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
stack->m_obj
 = v_res_2763_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkHeader___boxed(lean_object* v_className_2764_, lean_object* v_arity_2765_, lean_object* v_indVal_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Elab_Deriving_mkHeader(v_className_2764_, v_arity_2765_, v_indVal_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_arity_2765_);
return v_res_2774_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(lean_object* v_a_2775_, size_t v_sz_2776_, size_t v_i_2777_, lean_object* v_bs_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___redArg(v_a_2775_, v_sz_2776_, v_i_2777_, v_bs_2778_, v___y_2783_);
return v___x_2786_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2775_ = stack[0].m_obj;
size_t v_sz_2776_ = stack[1].m_num;
size_t v_i_2777_ = stack[2].m_num;
lean_object* v_bs_2778_ = stack[3].m_obj;
lean_object* v___y_2779_ = stack[4].m_obj;
lean_object* v___y_2780_ = stack[5].m_obj;
lean_object* v___y_2781_ = stack[6].m_obj;
lean_object* v___y_2782_ = stack[7].m_obj;
lean_object* v___y_2783_ = stack[8].m_obj;
lean_object* v___y_2784_ = stack[9].m_obj;
lean_object* v_res_2787_;
v_res_2787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_2775_, v_sz_2776_, v_i_2777_, v_bs_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
stack->m_obj
 = v_res_2787_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0___boxed(lean_object* v_a_2788_, lean_object* v_sz_2789_, lean_object* v_i_2790_, lean_object* v_bs_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
size_t v_sz_boxed_2799_; size_t v_i_boxed_2800_; lean_object* v_res_2801_; 
v_sz_boxed_2799_ = lean_unbox_usize(v_sz_2789_);
lean_dec(v_sz_2789_);
v_i_boxed_2800_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkHeader_spec__0(v_a_2788_, v_sz_boxed_2799_, v_i_boxed_2800_, v_bs_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
return v_res_2801_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(lean_object* v_upperBound_2802_, lean_object* v_inst_2803_, lean_object* v_R_2804_, lean_object* v_a_2805_, lean_object* v_b_2806_, lean_object* v_c_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___redArg(v_upperBound_2802_, v_a_2805_, v_b_2806_, v___y_2812_, v___y_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2802_ = stack[0].m_obj;
lean_object* v_a_2805_ = stack[3].m_obj;
lean_object* v_b_2806_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[6].m_obj;
lean_object* v___y_2809_ = stack[7].m_obj;
lean_object* v___y_2810_ = stack[8].m_obj;
lean_object* v___y_2811_ = stack[9].m_obj;
lean_object* v___y_2812_ = stack[10].m_obj;
lean_object* v___y_2813_ = stack[11].m_obj;
lean_object* v_res_2816_;
v_res_2816_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(v_upperBound_2802_, lean_box(0), lean_box(0), v_a_2805_, v_b_2806_, lean_box(0), v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
stack->m_obj
 = v_res_2816_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1___boxed(lean_object* v_upperBound_2817_, lean_object* v_inst_2818_, lean_object* v_R_2819_, lean_object* v_a_2820_, lean_object* v_b_2821_, lean_object* v_c_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkHeader_spec__1(v_upperBound_2817_, v_inst_2818_, v_R_2819_, v_a_2820_, v_b_2821_, v_c_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_upperBound_2817_);
return v_res_2830_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(lean_object* v_a_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_array_2835_; lean_object* v_start_2836_; lean_object* v_stop_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2861_; 
v_array_2835_ = lean_ctor_get(v_a_2831_, 0);
v_start_2836_ = lean_ctor_get(v_a_2831_, 1);
v_stop_2837_ = lean_ctor_get(v_a_2831_, 2);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2839_ = v_a_2831_;
v_isShared_2840_ = v_isSharedCheck_2861_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_stop_2837_);
lean_inc(v_start_2836_);
lean_inc(v_array_2835_);
lean_dec(v_a_2831_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2861_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_nat_dec_lt(v_start_2836_, v_stop_2837_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
lean_del_object(v___x_2839_);
lean_dec(v_stop_2837_);
lean_dec(v_start_2836_);
lean_dec_ref(v_array_2835_);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2832_);
return v___x_2842_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2843_ = lean_unsigned_to_nat(1u);
v___x_2844_ = lean_nat_add(v_start_2836_, v___x_2843_);
lean_inc_ref(v_array_2835_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v___x_2844_);
v___x_2846_ = v___x_2839_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_array_2835_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_stop_2837_);
v___x_2846_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_array_fget(v_array_2835_, v_start_2836_);
lean_dec(v_start_2836_);
lean_dec_ref(v_array_2835_);
v___x_2848_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v___x_2847_, v___y_2833_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = lean_array_push(v_b_2832_, v_a_2849_);
v_a_2831_ = v___x_2846_;
v_b_2832_ = v___x_2850_;
goto _start;
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v___x_2846_);
lean_dec_ref(v_b_2832_);
v_a_2852_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2848_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2848_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2831_ = stack[0].m_obj;
lean_object* v_b_2832_ = stack[1].m_obj;
lean_object* v___y_2833_ = stack[2].m_obj;
lean_object* v_res_2862_;
v_res_2862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2831_, v_b_2832_, v___y_2833_);
stack->m_obj
 = v_res_2862_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg___boxed(lean_object* v_a_2863_, lean_object* v_b_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2863_, v_b_2864_, v___y_2865_);
lean_dec_ref(v___y_2865_);
return v_res_2867_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(size_t v_sz_2868_, size_t v_i_2869_, lean_object* v_bs_2870_, lean_object* v___y_2871_){
_start:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_usize_dec_lt(v_i_2869_, v_sz_2868_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_bs_2870_);
return v___x_2874_;
}
else
{
lean_object* v_v_2875_; lean_object* v___x_2876_; lean_object* v_bs_x27_2877_; lean_object* v___x_2878_; 
v_v_2875_ = lean_array_uget(v_bs_2870_, v_i_2869_);
v___x_2876_ = lean_unsigned_to_nat(0u);
v_bs_x27_2877_ = lean_array_uset(v_bs_2870_, v_i_2869_, v___x_2876_);
v___x_2878_ = l_Lean_Elab_Deriving_mkDiscr___redArg(v_v_2875_, v___y_2871_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; size_t v___x_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = ((size_t)1ULL);
v___x_2881_ = lean_usize_add(v_i_2869_, v___x_2880_);
v___x_2882_ = lean_array_uset(v_bs_x27_2877_, v_i_2869_, v_a_2879_);
v_i_2869_ = v___x_2881_;
v_bs_2870_ = v___x_2882_;
goto _start;
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec_ref(v_bs_x27_2877_);
v_a_2884_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2878_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2878_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2868_ = stack[0].m_num;
size_t v_i_2869_ = stack[1].m_num;
lean_object* v_bs_2870_ = stack[2].m_obj;
lean_object* v___y_2871_ = stack[3].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2868_, v_i_2869_, v_bs_2870_, v___y_2871_);
stack->m_obj
 = v_res_2892_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg___boxed(lean_object* v_sz_2893_, lean_object* v_i_2894_, lean_object* v_bs_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
size_t v_sz_boxed_2898_; size_t v_i_boxed_2899_; lean_object* v_res_2900_; 
v_sz_boxed_2898_ = lean_unbox_usize(v_sz_2893_);
lean_dec(v_sz_2893_);
v_i_boxed_2899_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_res_2900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_boxed_2898_, v_i_boxed_2899_, v_bs_2895_, v___y_2896_);
lean_dec_ref(v___y_2896_);
return v_res_2900_;
}
}
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object* v_header_2901_, lean_object* v_indVal_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_argNames_2910_; lean_object* v_targetNames_2911_; lean_object* v_numParams_2912_; lean_object* v___x_2913_; lean_object* v_discrs_2914_; lean_object* v_lower_2916_; lean_object* v_upper_2917_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_argNames_2910_ = lean_ctor_get(v_header_2901_, 1);
lean_inc_ref(v_argNames_2910_);
v_targetNames_2911_ = lean_ctor_get(v_header_2901_, 2);
lean_inc_ref(v_targetNames_2911_);
lean_dec_ref(v_header_2901_);
v_numParams_2912_ = lean_ctor_get(v_indVal_2902_, 1);
lean_inc(v_numParams_2912_);
lean_dec_ref(v_indVal_2902_);
v___x_2913_ = lean_unsigned_to_nat(0u);
v_discrs_2914_ = ((lean_object*)(l_Lean_Elab_Deriving_mkInstImplicitBinders___lam__0___closed__0));
v___x_2933_ = lean_array_get_size(v_argNames_2910_);
v___x_2934_ = lean_nat_dec_le(v_numParams_2912_, v___x_2913_);
if (v___x_2934_ == 0)
{
v_lower_2916_ = v_numParams_2912_;
v_upper_2917_ = v___x_2933_;
goto v___jp_2915_;
}
else
{
lean_dec(v_numParams_2912_);
v_lower_2916_ = v___x_2913_;
v_upper_2917_ = v___x_2933_;
goto v___jp_2915_;
}
v___jp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_Array_toSubarray___redArg(v_argNames_2910_, v_lower_2916_, v_upper_2917_);
v___x_2919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v___x_2918_, v_discrs_2914_, v_a_2907_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; size_t v_sz_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v_sz_2921_ = lean_array_size(v_targetNames_2911_);
v___x_2922_ = ((size_t)0ULL);
v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2921_, v___x_2922_, v_targetNames_2911_, v_a_2907_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = l_Array_append___redArg(v_a_2920_, v_a_2924_);
lean_dec(v_a_2924_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_dec(v_a_2920_);
return v___x_2923_;
}
}
else
{
lean_dec_ref(v_targetNames_2911_);
return v___x_2919_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Deriving_mkDiscrs_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_2901_ = stack[0].m_obj;
lean_object* v_indVal_2902_ = stack[1].m_obj;
lean_object* v_a_2903_ = stack[2].m_obj;
lean_object* v_a_2904_ = stack[3].m_obj;
lean_object* v_a_2905_ = stack[4].m_obj;
lean_object* v_a_2906_ = stack[5].m_obj;
lean_object* v_a_2907_ = stack[6].m_obj;
lean_object* v_a_2908_ = stack[7].m_obj;
lean_object* v_res_2935_;
v_res_2935_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2901_, v_indVal_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
stack->m_obj
 = v_res_2935_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkDiscrs___boxed(lean_object* v_header_2936_, lean_object* v_indVal_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2936_, v_indVal_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2945_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(lean_object* v_inst_2946_, lean_object* v_R_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_, lean_object* v_c_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___redArg(v_a_2948_, v_b_2949_, v___y_2955_);
return v___x_2958_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2948_ = stack[2].m_obj;
lean_object* v_b_2949_ = stack[3].m_obj;
lean_object* v___y_2951_ = stack[5].m_obj;
lean_object* v___y_2952_ = stack[6].m_obj;
lean_object* v___y_2953_ = stack[7].m_obj;
lean_object* v___y_2954_ = stack[8].m_obj;
lean_object* v___y_2955_ = stack[9].m_obj;
lean_object* v___y_2956_ = stack[10].m_obj;
lean_object* v_res_2959_;
v_res_2959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(lean_box(0), lean_box(0), v_a_2948_, v_b_2949_, lean_box(0), v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
stack->m_obj
 = v_res_2959_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0___boxed(lean_object* v_inst_2960_, lean_object* v_R_2961_, lean_object* v_a_2962_, lean_object* v_b_2963_, lean_object* v_c_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_mkDiscrs_spec__0(v_inst_2960_, v_R_2961_, v_a_2962_, v_b_2963_, v_c_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
return v_res_2972_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(size_t v_sz_2973_, size_t v_i_2974_, lean_object* v_bs_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___redArg(v_sz_2973_, v_i_2974_, v_bs_2975_, v___y_2980_);
return v___x_2983_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2973_ = stack[0].m_num;
size_t v_i_2974_ = stack[1].m_num;
lean_object* v_bs_2975_ = stack[2].m_obj;
lean_object* v___y_2976_ = stack[3].m_obj;
lean_object* v___y_2977_ = stack[4].m_obj;
lean_object* v___y_2978_ = stack[5].m_obj;
lean_object* v___y_2979_ = stack[6].m_obj;
lean_object* v___y_2980_ = stack[7].m_obj;
lean_object* v___y_2981_ = stack[8].m_obj;
lean_object* v_res_2984_;
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_2973_, v_i_2974_, v_bs_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
stack->m_obj
 = v_res_2984_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1___boxed(lean_object* v_sz_2985_, lean_object* v_i_2986_, lean_object* v_bs_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
size_t v_sz_boxed_2995_; size_t v_i_boxed_2996_; lean_object* v_res_2997_; 
v_sz_boxed_2995_ = lean_unbox_usize(v_sz_2985_);
lean_dec(v_sz_2985_);
v_i_boxed_2996_ = lean_unbox_usize(v_i_2986_);
lean_dec(v_i_2986_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_mkDiscrs_spec__1(v_sz_boxed_2995_, v_i_boxed_2996_, v_bs_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2997_;
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
