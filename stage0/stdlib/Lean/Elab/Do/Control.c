// Lean compiler output
// Module: Lean.Elab.Do.Control
// Imports: import Lean.Meta.ProdN public import Lean.Elab.Do.Basic import Init.Control.Do
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Do_mkFreshResultType___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Do_MutVar_stateType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkProdN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getBreakCont___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_MutVar_stateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Do_bindMutVarsFromTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getContinueCont___redArg(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProdMkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_unStM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_unStM___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_unStM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_unStM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_unStM___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_unStM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Could not take apart "};
static const lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_unStM___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_unStM___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__3;
static const lean_string_object l_Lean_Elab_Do_ControlStack_unStM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " as a `"};
static const lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_unStM___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_unStM___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__5;
static const lean_string_object l_Lean_Elab_Do_ControlStack_unStM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`. This is a bug in the `do` elaborator."};
static const lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__6 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_unStM___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_unStM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_unStM___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "base"};
static const lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_ControlStack_base___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_ControlStack_base___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_ControlStack_base___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_base___closed__0_value;
static const lean_closure_object l_Lean_Elab_Do_ControlStack_base___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_ControlStack_base___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_ControlStack_base___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_base___closed__1_value;
static const lean_closure_object l_Lean_Elab_Do_ControlStack_base___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_ControlStack_base___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_ControlStack_base___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_base___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "StateT "};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " over "};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "State tuple type mismatch: expected "};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1;
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3;
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = ". This is a bug in the `do` elaborator."};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "StateT"};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 164, 216, 239, 139, 104, 41, 209)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OptionT"};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "run"};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 175, 92, 88, 165, 100, 98, 9)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 193, 54, 32, 53, 52, 46, 31)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "OptionT over "};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Except"};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 113, 136, 33, 237, 151, 233, 210)}};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ExceptT ("};
static const lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1;
static const lean_string_object l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ") over "};
static const lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ExceptT"};
static const lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 219, 228, 211, 167, 227, 255, 114)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 127, 229, 252, 62, 92, 31, 84)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "EarlyReturnT"};
static const lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 108, 71, 55, 35, 133, 242)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "EarlyReturn"};
static const lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "runK"};
static const lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 234, 189, 49, 36, 80, 19, 98)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value),LEAN_SCALAR_PTR_LITERAL(118, 43, 100, 225, 193, 181, 173, 166)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value;
static const lean_closure_object l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_getReturnCont___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "`break` must be nested inside a loop"};
static const lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_ControlStack_breakT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_ControlStack_breakT___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_breakT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BreakT"};
static const lean_object* l_Lean_Elab_Do_ControlStack_breakT___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_breakT___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 200, 41, 193, 137, 83, 48, 97)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_breakT___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_breakT___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Break"};
static const lean_object* l_Lean_Elab_Do_ControlStack_breakT___closed__3 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_breakT___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 204, 143, 3, 84, 67, 92, 151)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_breakT___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 178, 64, 100, 79, 118, 122, 28)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_breakT___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`continue` must be nested inside a loop"};
static const lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_ControlStack_continueT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_ControlStack_continueT___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_continueT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ContinueT"};
static const lean_object* l_Lean_Elab_Do_ControlStack_continueT___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_continueT___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 192, 244, 91, 192, 8, 248, 69)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_continueT___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_continueT___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Continue"};
static const lean_object* l_Lean_Elab_Do_ControlStack_continueT___closed__3 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_continueT___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 20, 42, 129, 129, 78, 218, 176)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_continueT___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value),LEAN_SCALAR_PTR_LITERAL(119, 220, 172, 113, 164, 208, 2, 169)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_continueT___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Monad"};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 218, 3, 131, 37, 173, 20, 218)}};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to synthesize "};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = " is not definitionally equal to "};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5;
static const lean_string_object l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkBreak___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkBreak___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_breakT___closed__1_value),LEAN_SCALAR_PTR_LITERAL(242, 200, 41, 193, 137, 83, 48, 97)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkBreak___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 247, 27, 233, 96, 191, 74, 131)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkBreak___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "break result type"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkBreak___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkContinue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "continue"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkContinue___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_continueT___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 192, 244, 91, 192, 8, 248, 69)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkContinue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 178, 162, 181, 231, 51, 24, 56)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkContinue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "continue result type"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkContinue___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkReturn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "δ"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkReturn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 55, 229, 44, 20, 64, 135, 12)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkReturn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "early return result type"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkReturn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___closed__3 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 108, 71, 55, 35, 133, 242)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(48, 121, 197, 158, 207, 131, 123, 195)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Applicative"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toPure"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__1 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 21, 170, 15, 195, 130, 155, 116)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 75, 18, 17, 200, 253, 193, 106)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__2 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toApplicative"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__3 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 218, 3, 131, 37, 173, 20, 218)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__3_value),LEAN_SCALAR_PTR_LITERAL(163, 196, 23, 87, 4, 45, 131, 42)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__4 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkPure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__5 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_ControlStack_mkPure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__6 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 135, 27, 238, 232, 181, 75, 85)}};
static const lean_ctor_object l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__6_value),LEAN_SCALAR_PTR_LITERAL(204, 106, 105, 165, 210, 13, 14, 1)}};
static const lean_object* l_Lean_Elab_Do_ControlStack_mkPure___closed__7 = (const lean_object*)&l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0 = (const lean_object*)&l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__2));
v___x_57_ = l_Lean_stringToMessageData(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__4));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__6));
v___x_63_ = l_Lean_stringToMessageData(v___x_62_);
return v___x_63_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_unStM(lean_object* v_m_64_, lean_object* v_stM_u03b1_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; 
v___x_74_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_75_ = 0;
v___x_76_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_74_, v___x_75_, v_a_66_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v_stM_78_; lean_object* v___x_79_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_n(v_a_77_, 2);
lean_dec_ref_known(v___x_76_, 1);
v_stM_78_ = lean_ctor_get(v_m_64_, 2);
lean_inc_ref(v_stM_78_);
lean_dec_ref(v_m_64_);
lean_inc(v_a_72_);
lean_inc_ref(v_a_71_);
lean_inc(v_a_70_);
lean_inc_ref(v_a_69_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc_ref(v_a_66_);
v___x_79_ = lean_apply_9(v_stM_78_, v_a_77_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, lean_box(0));
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_n(v_a_80_, 2);
lean_dec_ref_known(v___x_79_, 1);
lean_inc_ref(v_stM_u03b1_65_);
v___x_81_ = l_Lean_Meta_isExprDefEq(v_stM_u03b1_65_, v_a_80_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_108_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_108_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_108_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_108_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
uint8_t v___x_86_; 
v___x_86_ = lean_unbox(v_a_82_);
lean_dec(v_a_82_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_del_object(v___x_84_);
lean_dec(v_a_77_);
v___x_87_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__3, &l_Lean_Elab_Do_ControlStack_unStM___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3);
v___x_88_ = l_Lean_MessageData_ofExpr(v_stM_u03b1_65_);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__5, &l_Lean_Elab_Do_ControlStack_unStM___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_MessageData_ofExpr(v_a_80_);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__7, &l_Lean_Elab_Do_ControlStack_unStM___closed__7_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7);
v___x_95_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_95_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_object* v___x_106_; 
lean_dec(v_a_80_);
lean_dec_ref(v_stM_u03b1_65_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v_a_77_);
v___x_106_ = v___x_84_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_77_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec(v_a_80_);
lean_dec(v_a_77_);
lean_dec_ref(v_stM_u03b1_65_);
v_a_109_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_81_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_81_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
else
{
lean_dec(v_a_77_);
lean_dec_ref(v_stM_u03b1_65_);
return v___x_79_;
}
}
else
{
lean_dec_ref(v_stM_u03b1_65_);
lean_dec_ref(v_m_64_);
return v___x_76_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_unStM_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_64_ = stack[0].m_obj;
lean_object* v_stM_u03b1_65_ = stack[1].m_obj;
lean_object* v_a_66_ = stack[2].m_obj;
lean_object* v_a_67_ = stack[3].m_obj;
lean_object* v_a_68_ = stack[4].m_obj;
lean_object* v_a_69_ = stack[5].m_obj;
lean_object* v_a_70_ = stack[6].m_obj;
lean_object* v_a_71_ = stack[7].m_obj;
lean_object* v_a_72_ = stack[8].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Lean_Elab_Do_ControlStack_unStM(v_m_64_, v_stM_u03b1_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM___boxed(lean_object* v_m_118_, lean_object* v_stM_u03b1_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Elab_Do_ControlStack_unStM(v_m_118_, v_stM_u03b1_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_128_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(lean_object* v_00_u03b1_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_130_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_130_ = stack[1].m_obj;
lean_object* v___y_131_ = stack[2].m_obj;
lean_object* v___y_132_ = stack[3].m_obj;
lean_object* v___y_133_ = stack[4].m_obj;
lean_object* v___y_134_ = stack[5].m_obj;
lean_object* v___y_135_ = stack[6].m_obj;
lean_object* v___y_136_ = stack[7].m_obj;
lean_object* v___y_137_ = stack[8].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(lean_box(0), v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___boxed(lean_object* v_00_u03b1_141_, lean_object* v_msg_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(v_00_u03b1_141_, v_msg_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_151_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0(lean_object* v_dec_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v_dec_152_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_base___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_dec_152_ = stack[0].m_obj;
lean_object* v___y_153_ = stack[1].m_obj;
lean_object* v___y_154_ = stack[2].m_obj;
lean_object* v___y_155_ = stack[3].m_obj;
lean_object* v___y_156_ = stack[4].m_obj;
lean_object* v___y_157_ = stack[5].m_obj;
lean_object* v___y_158_ = stack[6].m_obj;
lean_object* v___y_159_ = stack[7].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_Elab_Do_ControlStack_base___lam__0(v_dec_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0___boxed(lean_object* v_dec_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Elab_Do_ControlStack_base___lam__0(v_dec_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_172_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1(lean_object* v_00_u03b1_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_00_u03b1_173_);
return v___x_182_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_base___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1_173_ = stack[0].m_obj;
lean_object* v___y_174_ = stack[1].m_obj;
lean_object* v___y_175_ = stack[2].m_obj;
lean_object* v___y_176_ = stack[3].m_obj;
lean_object* v___y_177_ = stack[4].m_obj;
lean_object* v___y_178_ = stack[5].m_obj;
lean_object* v___y_179_ = stack[6].m_obj;
lean_object* v___y_180_ = stack[7].m_obj;
lean_object* v_res_183_;
v_res_183_ = l_Lean_Elab_Do_ControlStack_base___lam__1(v_00_u03b1_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1___boxed(lean_object* v_00_u03b1_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Elab_Do_ControlStack_base___lam__1(v_00_u03b1_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1));
v___x_198_ = l_Lean_MessageData_ofFormat(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2(lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2, &l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once, _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2);
return v___x_200_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3(lean_object* v_m_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_m_201_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_base___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_201_ = stack[0].m_obj;
lean_object* v___y_202_ = stack[1].m_obj;
lean_object* v___y_203_ = stack[2].m_obj;
lean_object* v___y_204_ = stack[3].m_obj;
lean_object* v___y_205_ = stack[4].m_obj;
lean_object* v___y_206_ = stack[5].m_obj;
lean_object* v___y_207_ = stack[6].m_obj;
lean_object* v___y_208_ = stack[7].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Lean_Elab_Do_ControlStack_base___lam__3(v_m_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3___boxed(lean_object* v_m_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Do_ControlStack_base___lam__3(v_m_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base(lean_object* v_mi_225_){
_start:
{
lean_object* v_m_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_237_; 
v_m_226_ = lean_ctor_get(v_mi_225_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_mi_225_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_238_ = lean_ctor_get(v_mi_225_, 4);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_mi_225_, 3);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_mi_225_, 2);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_mi_225_, 1);
lean_dec(v_unused_241_);
v___x_228_ = v_mi_225_;
v_isShared_229_ = v_isSharedCheck_237_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_m_226_);
lean_dec(v_mi_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_237_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___x_235_; 
v___f_230_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__0));
v___f_231_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__1));
v___f_232_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__2));
v___f_233_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_base___lam__3___boxed), 9, 1);
lean_closure_set(v___f_233_, 0, v_m_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 4, v___f_230_);
lean_ctor_set(v___x_228_, 3, v___f_231_);
lean_ctor_set(v___x_228_, 2, v___f_231_);
lean_ctor_set(v___x_228_, 1, v___f_233_);
lean_ctor_set(v___x_228_, 0, v___f_232_);
v___x_235_ = v___x_228_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___f_232_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___f_233_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v___f_231_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v___f_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(size_t v_sz_242_, size_t v_i_243_, lean_object* v_bs_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_243_, v_sz_242_);
if (v___x_245_ == 0)
{
return v_bs_244_;
}
else
{
lean_object* v_v_246_; lean_object* v___x_247_; lean_object* v_bs_x27_248_; lean_object* v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; 
v_v_246_ = lean_array_uget(v_bs_244_, v_i_243_);
v___x_247_ = lean_unsigned_to_nat(0u);
v_bs_x27_248_ = lean_array_uset(v_bs_244_, v_i_243_, v___x_247_);
v___x_249_ = l_Lean_Elab_Do_MutVar_getId(v_v_246_);
lean_dec(v_v_246_);
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_243_, v___x_250_);
v___x_252_ = lean_array_uset(v_bs_x27_248_, v_i_243_, v___x_249_);
v_i_243_ = v___x_251_;
v_bs_244_ = v___x_252_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_242_ = stack[0].m_num;
size_t v_i_243_ = stack[1].m_num;
lean_object* v_bs_244_ = stack[2].m_obj;
lean_object* v_res_254_;
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_242_, v_i_243_, v_bs_244_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0___boxed(lean_object* v_sz_255_, lean_object* v_i_256_, lean_object* v_bs_257_){
_start:
{
size_t v_sz_boxed_258_; size_t v_i_boxed_259_; lean_object* v_res_260_; 
v_sz_boxed_258_ = lean_unbox_usize(v_sz_255_);
lean_dec(v_sz_255_);
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_boxed_258_, v_i_boxed_259_, v_bs_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(lean_object* v_muts_261_){
_start:
{
size_t v_sz_262_; size_t v___x_263_; lean_object* v___x_264_; 
v_sz_262_ = lean_array_size(v_muts_261_);
v___x_263_ = ((size_t)0ULL);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_262_, v___x_263_, v_muts_261_);
return v___x_264_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(size_t v_sz_265_, size_t v_i_266_, lean_object* v_bs_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_usize_dec_lt(v_i_266_, v_sz_265_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_bs_267_);
return v___x_274_;
}
else
{
lean_object* v_v_275_; lean_object* v___x_276_; lean_object* v_bs_x27_277_; lean_object* v___x_278_; 
v_v_275_ = lean_array_uget(v_bs_267_, v_i_266_);
v___x_276_ = lean_unsigned_to_nat(0u);
v_bs_x27_277_ = lean_array_uset(v_bs_267_, v_i_266_, v___x_276_);
v___x_278_ = l_Lean_Elab_Do_MutVar_stateType(v_v_275_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v_v_275_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_266_, v___x_280_);
v___x_282_ = lean_array_uset(v_bs_x27_277_, v_i_266_, v_a_279_);
v_i_266_ = v___x_281_;
v_bs_267_ = v___x_282_;
goto _start;
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_bs_x27_277_);
v_a_284_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_278_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_278_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_265_ = stack[0].m_num;
size_t v_i_266_ = stack[1].m_num;
lean_object* v_bs_267_ = stack[2].m_obj;
lean_object* v___y_268_ = stack[3].m_obj;
lean_object* v___y_269_ = stack[4].m_obj;
lean_object* v___y_270_ = stack[5].m_obj;
lean_object* v___y_271_ = stack[6].m_obj;
lean_object* v_res_292_;
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_265_, v_i_266_, v_bs_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg___boxed(lean_object* v_sz_293_, lean_object* v_i_294_, lean_object* v_bs_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
size_t v_sz_boxed_301_; size_t v_i_boxed_302_; lean_object* v_res_303_; 
v_sz_boxed_301_ = lean_unbox_usize(v_sz_293_);
lean_dec(v_sz_293_);
v_i_boxed_302_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_res_303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_boxed_301_, v_i_boxed_302_, v_bs_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_303_;
}
}
lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(lean_object* v_baseMonadInfo_304_, lean_object* v_muts_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
size_t v_sz_314_; size_t v___x_315_; lean_object* v___x_316_; 
v_sz_314_ = lean_array_size(v_muts_305_);
v___x_315_ = ((size_t)0ULL);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_314_, v___x_315_, v_muts_305_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v_u_318_; lean_object* v___x_319_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v_u_318_ = lean_ctor_get(v_baseMonadInfo_304_, 1);
lean_inc(v_u_318_);
lean_dec_ref(v_baseMonadInfo_304_);
v___x_319_ = l_Lean_Meta_mkProdN(v_a_317_, v_u_318_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
return v___x_319_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_baseMonadInfo_304_);
v_a_320_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_316_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_316_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseMonadInfo_304_ = stack[0].m_obj;
lean_object* v_muts_305_ = stack[1].m_obj;
lean_object* v_a_306_ = stack[2].m_obj;
lean_object* v_a_307_ = stack[3].m_obj;
lean_object* v_a_308_ = stack[4].m_obj;
lean_object* v_a_309_ = stack[5].m_obj;
lean_object* v_a_310_ = stack[6].m_obj;
lean_object* v_a_311_ = stack[7].m_obj;
lean_object* v_a_312_ = stack[8].m_obj;
lean_object* v_res_328_;
v_res_328_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_304_, v_muts_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3___boxed(lean_object* v_baseMonadInfo_329_, lean_object* v_muts_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_329_, v_muts_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_339_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(size_t v_sz_340_, size_t v_i_341_, lean_object* v_bs_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_340_, v_i_341_, v_bs_342_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v___x_351_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_340_ = stack[0].m_num;
size_t v_i_341_ = stack[1].m_num;
lean_object* v_bs_342_ = stack[2].m_obj;
lean_object* v___y_343_ = stack[3].m_obj;
lean_object* v___y_344_ = stack[4].m_obj;
lean_object* v___y_345_ = stack[5].m_obj;
lean_object* v___y_346_ = stack[6].m_obj;
lean_object* v___y_347_ = stack[7].m_obj;
lean_object* v___y_348_ = stack[8].m_obj;
lean_object* v___y_349_ = stack[9].m_obj;
lean_object* v_res_352_;
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(v_sz_340_, v_i_341_, v_bs_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___boxed(lean_object* v_sz_353_, lean_object* v_i_354_, lean_object* v_bs_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
size_t v_sz_boxed_364_; size_t v_i_boxed_365_; lean_object* v_res_366_; 
v_sz_boxed_364_ = lean_unbox_usize(v_sz_353_);
lean_dec(v_sz_353_);
v_i_boxed_365_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(v_sz_boxed_364_, v_i_boxed_365_, v_bs_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_366_;
}
}
lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(lean_object* v_baseMonadInfo_370_, lean_object* v_muts_371_, lean_object* v_00_u03b1_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
lean_inc_ref(v_baseMonadInfo_370_);
v___x_381_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_370_, v_muts_371_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_396_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_396_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_396_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_396_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_u_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v_u_386_ = lean_ctor_get(v_baseMonadInfo_370_, 1);
lean_inc_n(v_u_386_, 2);
lean_dec_ref(v_baseMonadInfo_370_);
v___x_387_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1));
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_u_386_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v_u_386_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_mkConst(v___x_387_, v___x_390_);
v___x_392_ = l_Lean_mkAppB(v___x_391_, v_00_u03b1_372_, v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_392_);
v___x_394_ = v___x_384_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_dec_ref(v_00_u03b1_372_);
lean_dec_ref(v_baseMonadInfo_370_);
return v___x_381_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseMonadInfo_370_ = stack[0].m_obj;
lean_object* v_muts_371_ = stack[1].m_obj;
lean_object* v_00_u03b1_372_ = stack[2].m_obj;
lean_object* v_a_373_ = stack[3].m_obj;
lean_object* v_a_374_ = stack[4].m_obj;
lean_object* v_a_375_ = stack[5].m_obj;
lean_object* v_a_376_ = stack[6].m_obj;
lean_object* v_a_377_ = stack[7].m_obj;
lean_object* v_a_378_ = stack[8].m_obj;
lean_object* v_a_379_ = stack[9].m_obj;
lean_object* v_res_397_;
v_res_397_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_370_, v_muts_371_, v_00_u03b1_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___boxed(lean_object* v_baseMonadInfo_398_, lean_object* v_muts_399_, lean_object* v_00_u03b1_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_398_, v_muts_399_, v_00_u03b1_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0(lean_object* v_base_416_, lean_object* v_00_u03c3_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_description_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_description_419_ = lean_ctor_get(v_base_416_, 0);
lean_inc_ref(v_description_419_);
lean_dec_ref(v_base_416_);
v___x_420_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1);
v___x_421_ = l_Lean_MessageData_ofExpr(v_00_u03c3_417_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_apply_1(v_description_419_, v___x_425_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_424_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
return v___x_427_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1(lean_object* v_base_428_, lean_object* v_baseMonadInfo_429_, lean_object* v_muts_430_, lean_object* v_00_u03b1_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_stM_440_; lean_object* v___x_441_; 
v_stM_440_ = lean_ctor_get(v_base_428_, 2);
lean_inc_ref(v_stM_440_);
lean_dec_ref(v_base_428_);
v___x_441_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_429_, v_muts_430_, v_00_u03b1_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc_ref(v___y_432_);
v___x_443_ = lean_apply_9(v_stM_440_, v_a_442_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
return v___x_443_;
}
else
{
lean_dec_ref(v_stM_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_stateT___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_base_428_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_429_ = stack[1].m_obj;
lean_object* v_muts_430_ = stack[2].m_obj;
lean_object* v_00_u03b1_431_ = stack[3].m_obj;
lean_object* v___y_432_ = stack[4].m_obj;
lean_object* v___y_433_ = stack[5].m_obj;
lean_object* v___y_434_ = stack[6].m_obj;
lean_object* v___y_435_ = stack[7].m_obj;
lean_object* v___y_436_ = stack[8].m_obj;
lean_object* v___y_437_ = stack[9].m_obj;
lean_object* v___y_438_ = stack[10].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(v_base_428_, v_baseMonadInfo_429_, v_muts_430_, v_00_u03b1_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(lean_object* v_base_445_, lean_object* v_baseMonadInfo_446_, lean_object* v_muts_447_, lean_object* v_00_u03b1_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(v_base_445_, v_baseMonadInfo_446_, v_muts_447_, v_00_u03b1_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_457_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2(lean_object* v_a_458_, lean_object* v_muts_459_, lean_object* v_resultName_460_, lean_object* v_k_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_getFVarFromUserName(v_a_458_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_muts_459_);
v___x_473_ = lean_array_to_list(v___x_472_);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v_resultName_460_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_Expr_fvarId_x21(v_a_471_);
lean_dec(v_a_471_);
v___x_476_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___x_474_, v___x_475_, v_k_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_476_;
}
else
{
lean_dec_ref(v_k_461_);
lean_dec(v_resultName_460_);
lean_dec_ref(v_muts_459_);
return v___x_470_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_stateT___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_458_ = stack[0].m_obj;
lean_object* v_muts_459_ = stack[1].m_obj;
lean_object* v_resultName_460_ = stack[2].m_obj;
lean_object* v_k_461_ = stack[3].m_obj;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v___y_464_ = stack[6].m_obj;
lean_object* v___y_465_ = stack[7].m_obj;
lean_object* v___y_466_ = stack[8].m_obj;
lean_object* v___y_467_ = stack[9].m_obj;
lean_object* v___y_468_ = stack[10].m_obj;
lean_object* v_res_477_;
v_res_477_ = l_Lean_Elab_Do_ControlStack_stateT___lam__2(v_a_458_, v_muts_459_, v_resultName_460_, v_k_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
stack->m_obj
 = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed(lean_object* v_a_478_, lean_object* v_muts_479_, lean_object* v_resultName_480_, lean_object* v_k_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Elab_Do_ControlStack_stateT___lam__2(v_a_478_, v_muts_479_, v_resultName_480_, v_k_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_490_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3(lean_object* v_muts_494_, lean_object* v_baseMonadInfo_495_, lean_object* v_base_496_, lean_object* v_dec_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1));
v___x_507_ = l_Lean_Core_mkFreshUserName(v___x_506_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v_resultName_509_; lean_object* v_resultType_510_; lean_object* v_k_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_532_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v_resultName_509_ = lean_ctor_get(v_dec_497_, 0);
v_resultType_510_ = lean_ctor_get(v_dec_497_, 1);
v_k_511_ = lean_ctor_get(v_dec_497_, 2);
v_isSharedCheck_532_ = !lean_is_exclusive(v_dec_497_);
if (v_isSharedCheck_532_ == 0)
{
v___x_513_ = v_dec_497_;
v_isShared_514_ = v_isSharedCheck_532_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_k_511_);
lean_inc(v_resultType_510_);
lean_inc(v_resultName_509_);
lean_dec(v_dec_497_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_532_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___f_515_; lean_object* v___x_516_; 
lean_inc_ref(v_muts_494_);
lean_inc(v_a_508_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed), 12, 4);
lean_closure_set(v___f_515_, 0, v_a_508_);
lean_closure_set(v___f_515_, 1, v_muts_494_);
lean_closure_set(v___f_515_, 2, v_resultName_509_);
lean_closure_set(v___f_515_, 3, v_k_511_);
v___x_516_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_495_, v_muts_494_, v_resultType_510_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v_restoreCont_518_; uint8_t v___x_519_; lean_object* v___x_521_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v_restoreCont_518_ = lean_ctor_get(v_base_496_, 4);
lean_inc_ref(v_restoreCont_518_);
lean_dec_ref(v_base_496_);
v___x_519_ = 0;
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 2, v___f_515_);
lean_ctor_set(v___x_513_, 1, v_a_517_);
lean_ctor_set(v___x_513_, 0, v_a_508_);
v___x_521_ = v___x_513_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_a_517_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v___f_515_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*3, v___x_519_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_498_);
v___x_522_ = lean_apply_9(v_restoreCont_518_, v___x_521_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
return v___x_522_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v___f_515_);
lean_del_object(v___x_513_);
lean_dec(v_a_508_);
lean_dec_ref(v_base_496_);
v_a_524_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_516_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_516_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_dec_497_);
lean_dec_ref(v_base_496_);
lean_dec_ref(v_baseMonadInfo_495_);
lean_dec_ref(v_muts_494_);
v_a_533_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_507_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_507_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_stateT___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_muts_494_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_495_ = stack[1].m_obj;
lean_object* v_base_496_ = stack[2].m_obj;
lean_object* v_dec_497_ = stack[3].m_obj;
lean_object* v___y_498_ = stack[4].m_obj;
lean_object* v___y_499_ = stack[5].m_obj;
lean_object* v___y_500_ = stack[6].m_obj;
lean_object* v___y_501_ = stack[7].m_obj;
lean_object* v___y_502_ = stack[8].m_obj;
lean_object* v___y_503_ = stack[9].m_obj;
lean_object* v___y_504_ = stack[10].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(v_muts_494_, v_baseMonadInfo_495_, v_base_496_, v_dec_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(lean_object* v_muts_542_, lean_object* v_baseMonadInfo_543_, lean_object* v_base_544_, lean_object* v_dec_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(v_muts_542_, v_baseMonadInfo_543_, v_base_544_, v_dec_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_554_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(size_t v_sz_555_, size_t v_i_556_, lean_object* v_bs_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = lean_usize_dec_lt(v_i_556_, v_sz_555_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_bs_557_);
return v___x_566_;
}
else
{
lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_bs_x27_569_; lean_object* v___y_571_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_v_567_ = lean_array_uget(v_bs_557_, v_i_556_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_bs_x27_569_ = lean_array_uset(v_bs_557_, v_i_556_, v___x_568_);
v___x_585_ = l_Lean_Elab_Do_MutVar_getId(v_v_567_);
v___x_586_ = l_Lean_Meta_getFVarFromUserName(v___x_585_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v_ident_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v_ident_588_ = lean_ctor_get(v_v_567_, 0);
v___x_589_ = lean_box(0);
v___x_590_ = lean_box(0);
v___x_591_ = 0;
lean_inc(v_ident_588_);
v___x_592_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_588_, v_a_587_, v___x_589_, v___x_589_, v___x_590_, v___x_591_, v___x_591_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_593_; 
lean_dec_ref_known(v___x_592_, 1);
v___x_593_ = l_Lean_Elab_Do_MutVar_stateValue(v_v_567_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v_v_567_);
v___y_571_ = v___x_593_;
goto v___jp_570_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_bs_x27_569_);
lean_dec(v_v_567_);
v_a_594_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_592_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_dec(v_v_567_);
v___y_571_ = v___x_586_;
goto v___jp_570_;
}
v___jp_570_:
{
if (lean_obj_tag(v___y_571_) == 0)
{
lean_object* v_a_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_a_572_ = lean_ctor_get(v___y_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___y_571_, 1);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_556_, v___x_573_);
v___x_575_ = lean_array_uset(v_bs_x27_569_, v_i_556_, v_a_572_);
v_i_556_ = v___x_574_;
v_bs_557_ = v___x_575_;
goto _start;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v_bs_x27_569_);
v_a_577_ = lean_ctor_get(v___y_571_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___y_571_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___y_571_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___y_571_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_555_ = stack[0].m_num;
size_t v_i_556_ = stack[1].m_num;
lean_object* v_bs_557_ = stack[2].m_obj;
lean_object* v___y_558_ = stack[3].m_obj;
lean_object* v___y_559_ = stack[4].m_obj;
lean_object* v___y_560_ = stack[5].m_obj;
lean_object* v___y_561_ = stack[6].m_obj;
lean_object* v___y_562_ = stack[7].m_obj;
lean_object* v___y_563_ = stack[8].m_obj;
lean_object* v_res_602_;
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_555_, v_i_556_, v_bs_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object* v_sz_603_, lean_object* v_i_604_, lean_object* v_bs_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v_i_boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v_i_boxed_614_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_613_, v_i_boxed_614_, v_bs_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object* v_muts_625_, lean_object* v_baseMonadInfo_626_, lean_object* v_base_627_, lean_object* v_00_u03c3_628_, lean_object* v_e_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
size_t v_sz_638_; size_t v___x_639_; lean_object* v___x_640_; 
v_sz_638_ = lean_array_size(v_muts_625_);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_638_, v___x_639_, v_muts_625_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v_u_642_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v_u_642_ = lean_ctor_get(v_baseMonadInfo_626_, 1);
lean_inc(v_u_642_);
lean_dec_ref(v_baseMonadInfo_626_);
v___x_643_ = l_Lean_Meta_mkProdMkN(v_a_641_, v_u_642_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v_fst_645_; lean_object* v_snd_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_692_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v_fst_645_ = lean_ctor_get(v_a_644_, 0);
v_snd_646_ = lean_ctor_get(v_a_644_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_692_ == 0)
{
v___x_648_ = v_a_644_;
v_isShared_649_ = v_isSharedCheck_692_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_snd_646_);
lean_inc(v_fst_645_);
lean_dec(v_a_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_692_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___x_661_; 
lean_inc_ref(v_00_u03c3_628_);
lean_inc(v_snd_646_);
v___x_661_ = l_Lean_Meta_isExprDefEq(v_snd_646_, v_00_u03c3_628_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; uint8_t v___x_663_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_unbox(v_a_662_);
lean_dec(v_a_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_fst_645_);
lean_dec_ref(v_e_629_);
lean_dec_ref(v_base_627_);
v___x_664_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1);
v___x_665_ = l_Lean_MessageData_ofExpr(v_00_u03c3_628_);
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 7);
lean_ctor_set(v___x_648_, 1, v___x_665_);
lean_ctor_set(v___x_648_, 0, v___x_664_);
v___x_667_ = v___x_648_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_683_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v___x_668_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_MessageData_ofExpr(v_snd_646_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_673_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_del_object(v___x_648_);
lean_dec(v_snd_646_);
lean_dec_ref(v_00_u03c3_628_);
v___y_651_ = v___y_630_;
v___y_652_ = v___y_631_;
v___y_653_ = v___y_632_;
v___y_654_ = v___y_633_;
v___y_655_ = v___y_634_;
v___y_656_ = v___y_635_;
v___y_657_ = v___y_636_;
goto v___jp_650_;
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_del_object(v___x_648_);
lean_dec(v_snd_646_);
lean_dec(v_fst_645_);
lean_dec_ref(v_e_629_);
lean_dec_ref(v_00_u03c3_628_);
lean_dec_ref(v_base_627_);
v_a_684_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_661_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_661_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
v___jp_650_:
{
lean_object* v_runInBase_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_runInBase_658_ = lean_ctor_get(v_base_627_, 3);
lean_inc_ref(v_runInBase_658_);
lean_dec_ref(v_base_627_);
v___x_659_ = l_Lean_Expr_app___override(v_e_629_, v_fst_645_);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
lean_inc_ref(v___y_651_);
v___x_660_ = lean_apply_9(v_runInBase_658_, v___x_659_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, lean_box(0));
return v___x_660_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_e_629_);
lean_dec_ref(v_00_u03c3_628_);
lean_dec_ref(v_base_627_);
v_a_693_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_643_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_643_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_e_629_);
lean_dec_ref(v_00_u03c3_628_);
lean_dec_ref(v_base_627_);
lean_dec_ref(v_baseMonadInfo_626_);
v_a_701_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_640_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_640_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_stateT___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_muts_625_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_626_ = stack[1].m_obj;
lean_object* v_base_627_ = stack[2].m_obj;
lean_object* v_00_u03c3_628_ = stack[3].m_obj;
lean_object* v_e_629_ = stack[4].m_obj;
lean_object* v___y_630_ = stack[5].m_obj;
lean_object* v___y_631_ = stack[6].m_obj;
lean_object* v___y_632_ = stack[7].m_obj;
lean_object* v___y_633_ = stack[8].m_obj;
lean_object* v___y_634_ = stack[9].m_obj;
lean_object* v___y_635_ = stack[10].m_obj;
lean_object* v___y_636_ = stack[11].m_obj;
lean_object* v_res_709_;
v_res_709_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_muts_625_, v_baseMonadInfo_626_, v_base_627_, v_00_u03c3_628_, v_e_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object* v_muts_710_, lean_object* v_baseMonadInfo_711_, lean_object* v_base_712_, lean_object* v_00_u03c3_713_, lean_object* v_e_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_muts_710_, v_baseMonadInfo_711_, v_base_712_, v_00_u03c3_713_, v_e_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_723_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object* v_baseMonadInfo_727_, lean_object* v_muts_728_, lean_object* v_base_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc_ref(v_baseMonadInfo_727_);
v___x_738_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_727_, v_muts_728_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v_m_740_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v_m_740_ = lean_ctor_get(v_base_729_, 1);
lean_inc_ref(v_m_740_);
lean_dec_ref(v_base_729_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc_ref(v___y_730_);
v___x_741_ = lean_apply_8(v_m_740_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_757_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_757_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_757_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_757_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_u_746_; lean_object* v_v_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v_u_746_ = lean_ctor_get(v_baseMonadInfo_727_, 1);
lean_inc(v_u_746_);
v_v_747_ = lean_ctor_get(v_baseMonadInfo_727_, 2);
lean_inc(v_v_747_);
lean_dec_ref(v_baseMonadInfo_727_);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1));
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v_v_747_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v_u_746_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_mkConst(v___x_748_, v___x_751_);
v___x_753_ = l_Lean_mkAppB(v___x_752_, v_a_739_, v_a_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_753_);
v___x_755_ = v___x_744_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_dec(v_a_739_);
lean_dec_ref(v_baseMonadInfo_727_);
return v___x_741_;
}
}
else
{
lean_dec_ref(v_base_729_);
lean_dec_ref(v_baseMonadInfo_727_);
return v___x_738_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_stateT___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseMonadInfo_727_ = stack[0].m_obj;
lean_object* v_muts_728_ = stack[1].m_obj;
lean_object* v_base_729_ = stack[2].m_obj;
lean_object* v___y_730_ = stack[3].m_obj;
lean_object* v___y_731_ = stack[4].m_obj;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v___y_733_ = stack[6].m_obj;
lean_object* v___y_734_ = stack[7].m_obj;
lean_object* v___y_735_ = stack[8].m_obj;
lean_object* v___y_736_ = stack[9].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_727_, v_muts_728_, v_base_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object* v_baseMonadInfo_759_, lean_object* v_muts_760_, lean_object* v_base_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_759_, v_muts_760_, v_base_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object* v_baseMonadInfo_771_, lean_object* v_muts_772_, lean_object* v_00_u03c3_773_, lean_object* v_base_774_){
_start:
{
lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
lean_inc_ref(v_00_u03c3_773_);
lean_inc_ref_n(v_base_774_, 4);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0), 3, 2);
lean_closure_set(v___f_775_, 0, v_base_774_);
lean_closure_set(v___f_775_, 1, v_00_u03c3_773_);
lean_inc_ref_n(v_muts_772_, 3);
lean_inc_ref_n(v_baseMonadInfo_771_, 3);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed), 12, 3);
lean_closure_set(v___f_776_, 0, v_base_774_);
lean_closure_set(v___f_776_, 1, v_baseMonadInfo_771_);
lean_closure_set(v___f_776_, 2, v_muts_772_);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed), 12, 3);
lean_closure_set(v___f_777_, 0, v_muts_772_);
lean_closure_set(v___f_777_, 1, v_baseMonadInfo_771_);
lean_closure_set(v___f_777_, 2, v_base_774_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed), 13, 4);
lean_closure_set(v___f_778_, 0, v_muts_772_);
lean_closure_set(v___f_778_, 1, v_baseMonadInfo_771_);
lean_closure_set(v___f_778_, 2, v_base_774_);
lean_closure_set(v___f_778_, 3, v_00_u03c3_773_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed), 11, 3);
lean_closure_set(v___f_779_, 0, v_baseMonadInfo_771_);
lean_closure_set(v___f_779_, 1, v_muts_772_);
lean_closure_set(v___f_779_, 2, v_base_774_);
v___x_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_780_, 0, v___f_775_);
lean_ctor_set(v___x_780_, 1, v___f_779_);
lean_ctor_set(v___x_780_, 2, v___f_776_);
lean_ctor_set(v___x_780_, 3, v___f_778_);
lean_ctor_set(v___x_780_, 4, v___f_777_);
return v___x_780_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t v_sz_781_, size_t v_i_782_, lean_object* v_bs_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_781_, v_i_782_, v_bs_783_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_781_ = stack[0].m_num;
size_t v_i_782_ = stack[1].m_num;
lean_object* v_bs_783_ = stack[2].m_obj;
lean_object* v___y_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v___y_786_ = stack[5].m_obj;
lean_object* v___y_787_ = stack[6].m_obj;
lean_object* v___y_788_ = stack[7].m_obj;
lean_object* v___y_789_ = stack[8].m_obj;
lean_object* v___y_790_ = stack[9].m_obj;
lean_object* v_res_793_;
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_781_, v_i_782_, v_bs_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object* v_sz_794_, lean_object* v_i_795_, lean_object* v_bs_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_794_);
lean_dec(v_sz_794_);
v_i_boxed_806_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_805_, v_i_boxed_806_, v_bs_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object* v_baseMonadInfo_811_, lean_object* v_00_u03b1_812_){
_start:
{
lean_object* v_u_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_u_813_ = lean_ctor_get(v_baseMonadInfo_811_, 1);
v___x_814_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_815_ = lean_box(0);
lean_inc(v_u_813_);
v___x_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_816_, 0, v_u_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_mkConst(v___x_814_, v___x_816_);
v___x_818_ = l_Lean_Expr_app___override(v___x_817_, v_00_u03b1_812_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object* v_baseMonadInfo_819_, lean_object* v_00_u03b1_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_819_, v_00_u03b1_820_);
lean_dec_ref(v_baseMonadInfo_819_);
return v_res_821_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object* v_runInBase_827_, lean_object* v_e_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2));
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_mk_empty_array_with_capacity(v___x_838_);
v___x_840_ = lean_array_push(v___x_839_, v_e_828_);
v___x_841_ = l_Lean_Meta_mkAppM(v___x_837_, v___x_840_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_843_ = lean_apply_9(v_runInBase_827_, v_a_842_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
return v___x_843_;
}
else
{
lean_dec_ref(v_runInBase_827_);
return v___x_841_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_runInBase_827_ = stack[0].m_obj;
lean_object* v_e_828_ = stack[1].m_obj;
lean_object* v___y_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v___y_831_ = stack[4].m_obj;
lean_object* v___y_832_ = stack[5].m_obj;
lean_object* v___y_833_ = stack[6].m_obj;
lean_object* v___y_834_ = stack[7].m_obj;
lean_object* v___y_835_ = stack[8].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_827_, v_e_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object* v_runInBase_845_, lean_object* v_e_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_845_, v_e_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_855_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object* v_description_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1, &l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1);
v___x_862_ = lean_box(0);
v___x_863_ = lean_apply_1(v_description_859_, v___x_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_861_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
return v___x_864_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object* v_dec_865_, lean_object* v_r_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_k_875_; lean_object* v___x_876_; 
v_k_875_ = lean_ctor_get(v_dec_865_, 2);
lean_inc_ref(v_k_875_);
lean_dec_ref(v_dec_865_);
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc_ref(v___y_867_);
v___x_876_ = lean_apply_8(v_k_875_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, lean_box(0));
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; uint8_t v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_878_);
v___x_880_ = lean_array_push(v___x_879_, v_r_866_);
v___x_881_ = 0;
v___x_882_ = 1;
v___x_883_ = 1;
v___x_884_ = l_Lean_Meta_mkLambdaFVars(v___x_880_, v_a_877_, v___x_881_, v___x_882_, v___x_881_, v___x_882_, v___x_883_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec_ref(v___x_880_);
return v___x_884_;
}
else
{
lean_dec_ref(v_r_866_);
return v___x_876_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_dec_865_ = stack[0].m_obj;
lean_object* v_r_866_ = stack[1].m_obj;
lean_object* v___y_867_ = stack[2].m_obj;
lean_object* v___y_868_ = stack[3].m_obj;
lean_object* v___y_869_ = stack[4].m_obj;
lean_object* v___y_870_ = stack[5].m_obj;
lean_object* v___y_871_ = stack[6].m_obj;
lean_object* v___y_872_ = stack[7].m_obj;
lean_object* v___y_873_ = stack[8].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_dec_865_, v_r_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object* v_dec_886_, lean_object* v_r_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_dec_886_, v_r_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_896_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object* v_a_897_, lean_object* v_r_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc_ref(v___y_899_);
v___x_907_ = lean_apply_8(v_a_897_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, lean_box(0));
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; uint8_t v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_mk_empty_array_with_capacity(v___x_909_);
v___x_911_ = lean_array_push(v___x_910_, v_r_898_);
v___x_912_ = 0;
v___x_913_ = 1;
v___x_914_ = 1;
v___x_915_ = l_Lean_Meta_mkLambdaFVars(v___x_911_, v_a_908_, v___x_912_, v___x_913_, v___x_912_, v___x_913_, v___x_914_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec_ref(v___x_911_);
return v___x_915_;
}
else
{
lean_dec_ref(v_r_898_);
return v___x_907_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_897_ = stack[0].m_obj;
lean_object* v_r_898_ = stack[1].m_obj;
lean_object* v___y_899_ = stack[2].m_obj;
lean_object* v___y_900_ = stack[3].m_obj;
lean_object* v___y_901_ = stack[4].m_obj;
lean_object* v___y_902_ = stack[5].m_obj;
lean_object* v___y_903_ = stack[6].m_obj;
lean_object* v___y_904_ = stack[7].m_obj;
lean_object* v___y_905_ = stack[8].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_897_, v_r_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object* v_a_917_, lean_object* v_r_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_917_, v_r_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_927_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object* v_k_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc_ref(v___y_929_);
v___x_938_ = lean_apply_9(v_k_928_, v_b_932_, v___y_929_, v___y_930_, v___y_931_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, lean_box(0));
return v___x_938_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_928_ = stack[0].m_obj;
lean_object* v___y_929_ = stack[1].m_obj;
lean_object* v___y_930_ = stack[2].m_obj;
lean_object* v___y_931_ = stack[3].m_obj;
lean_object* v_b_932_ = stack[4].m_obj;
lean_object* v___y_933_ = stack[5].m_obj;
lean_object* v___y_934_ = stack[6].m_obj;
lean_object* v___y_935_ = stack[7].m_obj;
lean_object* v___y_936_ = stack[8].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_928_, v___y_929_, v___y_930_, v___y_931_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v_b_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_940_, v___y_941_, v___y_942_, v___y_943_, v_b_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_950_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object* v_name_951_, uint8_t v_bi_952_, lean_object* v_type_953_, lean_object* v_k_954_, uint8_t v_kind_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___f_964_; lean_object* v___x_965_; 
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc_ref(v___y_956_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_964_, 0, v_k_954_);
lean_closure_set(v___f_964_, 1, v___y_956_);
lean_closure_set(v___f_964_, 2, v___y_957_);
lean_closure_set(v___f_964_, 3, v___y_958_);
v___x_965_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_951_, v_bi_952_, v_type_953_, v___f_964_, v_kind_955_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_965_) == 0)
{
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_951_ = stack[0].m_obj;
uint8_t v_bi_952_ = stack[1].m_num;
lean_object* v_type_953_ = stack[2].m_obj;
lean_object* v_k_954_ = stack[3].m_obj;
uint8_t v_kind_955_ = stack[4].m_num;
lean_object* v___y_956_ = stack[5].m_obj;
lean_object* v___y_957_ = stack[6].m_obj;
lean_object* v___y_958_ = stack[7].m_obj;
lean_object* v___y_959_ = stack[8].m_obj;
lean_object* v___y_960_ = stack[9].m_obj;
lean_object* v___y_961_ = stack[10].m_obj;
lean_object* v___y_962_ = stack[11].m_obj;
lean_object* v_res_974_;
v_res_974_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_951_, v_bi_952_, v_type_953_, v_k_954_, v_kind_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
stack->m_obj
 = v_res_974_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object* v_name_975_, lean_object* v_bi_976_, lean_object* v_type_977_, lean_object* v_k_978_, lean_object* v_kind_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_bi_boxed_988_; uint8_t v_kind_boxed_989_; lean_object* v_res_990_; 
v_bi_boxed_988_ = lean_unbox(v_bi_976_);
v_kind_boxed_989_ = lean_unbox(v_kind_979_);
v_res_990_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_975_, v_bi_boxed_988_, v_type_977_, v_k_978_, v_kind_boxed_989_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_990_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object* v_name_991_, lean_object* v_type_992_, lean_object* v_k_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
uint8_t v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = 0;
v___x_1003_ = 0;
v___x_1004_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_991_, v___x_1002_, v_type_992_, v_k_993_, v___x_1003_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1004_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_991_ = stack[0].m_obj;
lean_object* v_type_992_ = stack[1].m_obj;
lean_object* v_k_993_ = stack[2].m_obj;
lean_object* v___y_994_ = stack[3].m_obj;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v___y_996_ = stack[5].m_obj;
lean_object* v___y_997_ = stack[6].m_obj;
lean_object* v___y_998_ = stack[7].m_obj;
lean_object* v___y_999_ = stack[8].m_obj;
lean_object* v___y_1000_ = stack[9].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_991_, v_type_992_, v_k_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object* v_name_1006_, lean_object* v_type_1007_, lean_object* v_k_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1006_, v_type_1007_, v_k_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3));
v___x_1026_ = l_Lean_mkConst(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object* v_a_1027_, lean_object* v_getCont_1028_, lean_object* v_resultName_1029_, lean_object* v_resultType_1030_, lean_object* v___f_1031_, lean_object* v_baseMonadInfo_1032_, lean_object* v_casesOnWrapper_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Meta_getFVarFromUserName(v_a_1027_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc_ref(v___y_1034_);
v___x_1044_ = lean_apply_8(v_getCont_1028_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1046_, 0, v_a_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1048_ = l_Lean_Core_mkFreshUserName(v___x_1047_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4, &l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4);
v___x_1052_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1049_, v___x_1051_, v___f_1046_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
lean_inc_ref(v_resultType_1030_);
v___x_1054_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1029_, v_resultType_1030_, v___f_1031_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v_doBlockResultType_1056_; lean_object* v___x_1057_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v_doBlockResultType_1056_ = lean_ctor_get(v___y_1034_, 3);
lean_inc_ref(v_doBlockResultType_1056_);
v___x_1057_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1056_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1071_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1071_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1071_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_u_1062_; lean_object* v_v_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v_u_1062_ = lean_ctor_get(v_baseMonadInfo_1032_, 1);
v_v_1063_ = lean_ctor_get(v_baseMonadInfo_1032_, 2);
lean_inc(v_v_1063_);
v___x_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_v_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1050_);
lean_inc(v_u_1062_);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_u_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_mkConst(v_casesOnWrapper_1033_, v___x_1065_);
v___x_1067_ = l_Lean_mkApp5(v___x_1066_, v_resultType_1030_, v_a_1058_, v_a_1043_, v_a_1053_, v_a_1055_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1067_);
v___x_1069_ = v___x_1060_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_dec(v_a_1055_);
lean_dec(v_a_1053_);
lean_dec(v_a_1043_);
lean_dec(v_casesOnWrapper_1033_);
lean_dec_ref(v_resultType_1030_);
return v___x_1057_;
}
}
else
{
lean_dec(v_a_1053_);
lean_dec(v_a_1043_);
lean_dec(v_casesOnWrapper_1033_);
lean_dec_ref(v_resultType_1030_);
return v___x_1054_;
}
}
else
{
lean_dec(v_a_1043_);
lean_dec(v_casesOnWrapper_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_resultType_1030_);
lean_dec(v_resultName_1029_);
return v___x_1052_;
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___f_1046_);
lean_dec(v_a_1043_);
lean_dec(v_casesOnWrapper_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_resultType_1030_);
lean_dec(v_resultName_1029_);
v_a_1072_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1048_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1048_);
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
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1043_);
lean_dec(v_casesOnWrapper_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_resultType_1030_);
lean_dec(v_resultName_1029_);
v_a_1080_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1044_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1044_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_dec(v_casesOnWrapper_1033_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_resultType_1030_);
lean_dec(v_resultName_1029_);
lean_dec_ref(v_getCont_1028_);
return v___x_1042_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1027_ = stack[0].m_obj;
lean_object* v_getCont_1028_ = stack[1].m_obj;
lean_object* v_resultName_1029_ = stack[2].m_obj;
lean_object* v_resultType_1030_ = stack[3].m_obj;
lean_object* v___f_1031_ = stack[4].m_obj;
lean_object* v_baseMonadInfo_1032_ = stack[5].m_obj;
lean_object* v_casesOnWrapper_1033_ = stack[6].m_obj;
lean_object* v___y_1034_ = stack[7].m_obj;
lean_object* v___y_1035_ = stack[8].m_obj;
lean_object* v___y_1036_ = stack[9].m_obj;
lean_object* v___y_1037_ = stack[10].m_obj;
lean_object* v___y_1038_ = stack[11].m_obj;
lean_object* v___y_1039_ = stack[12].m_obj;
lean_object* v___y_1040_ = stack[13].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1027_, v_getCont_1028_, v_resultName_1029_, v_resultType_1030_, v___f_1031_, v_baseMonadInfo_1032_, v_casesOnWrapper_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object* v_a_1089_, lean_object* v_getCont_1090_, lean_object* v_resultName_1091_, lean_object* v_resultType_1092_, lean_object* v___f_1093_, lean_object* v_baseMonadInfo_1094_, lean_object* v_casesOnWrapper_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1089_, v_getCont_1090_, v_resultName_1091_, v_resultType_1092_, v___f_1093_, v_baseMonadInfo_1094_, v_casesOnWrapper_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v_baseMonadInfo_1094_);
return v_res_1104_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object* v_getCont_1108_, lean_object* v_baseMonadInfo_1109_, lean_object* v_casesOnWrapper_1110_, lean_object* v_restoreCont_1111_, lean_object* v_dec_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_inc_ref(v_dec_1112_);
v___f_1121_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1121_, 0, v_dec_1112_);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1123_ = l_Lean_Core_mkFreshUserName(v___x_1122_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v_resultName_1125_; lean_object* v_resultType_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1137_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v_resultName_1125_ = lean_ctor_get(v_dec_1112_, 0);
v_resultType_1126_ = lean_ctor_get(v_dec_1112_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_dec_1112_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v_dec_1112_, 2);
lean_dec(v_unused_1138_);
v___x_1128_ = v_dec_1112_;
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_resultType_1126_);
lean_inc(v_resultName_1125_);
lean_dec(v_dec_1112_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1134_; 
lean_inc_ref(v_baseMonadInfo_1109_);
lean_inc_ref(v_resultType_1126_);
lean_inc(v_a_1124_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed), 15, 7);
lean_closure_set(v___f_1130_, 0, v_a_1124_);
lean_closure_set(v___f_1130_, 1, v_getCont_1108_);
lean_closure_set(v___f_1130_, 2, v_resultName_1125_);
lean_closure_set(v___f_1130_, 3, v_resultType_1126_);
lean_closure_set(v___f_1130_, 4, v___f_1121_);
lean_closure_set(v___f_1130_, 5, v_baseMonadInfo_1109_);
lean_closure_set(v___f_1130_, 6, v_casesOnWrapper_1110_);
v___x_1131_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1109_, v_resultType_1126_);
lean_dec_ref(v_baseMonadInfo_1109_);
v___x_1132_ = 0;
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v___f_1130_);
lean_ctor_set(v___x_1128_, 1, v___x_1131_);
lean_ctor_set(v___x_1128_, 0, v_a_1124_);
v___x_1134_ = v___x_1128_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v___f_1130_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; 
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*3, v___x_1132_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc_ref(v___y_1113_);
v___x_1135_ = lean_apply_9(v_restoreCont_1111_, v___x_1134_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, lean_box(0));
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___f_1121_);
lean_dec_ref(v_dec_1112_);
lean_dec_ref(v_restoreCont_1111_);
lean_dec(v_casesOnWrapper_1110_);
lean_dec_ref(v_baseMonadInfo_1109_);
lean_dec_ref(v_getCont_1108_);
v_a_1139_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1123_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1123_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_getCont_1108_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_1109_ = stack[1].m_obj;
lean_object* v_casesOnWrapper_1110_ = stack[2].m_obj;
lean_object* v_restoreCont_1111_ = stack[3].m_obj;
lean_object* v_dec_1112_ = stack[4].m_obj;
lean_object* v___y_1113_ = stack[5].m_obj;
lean_object* v___y_1114_ = stack[6].m_obj;
lean_object* v___y_1115_ = stack[7].m_obj;
lean_object* v___y_1116_ = stack[8].m_obj;
lean_object* v___y_1117_ = stack[9].m_obj;
lean_object* v___y_1118_ = stack[10].m_obj;
lean_object* v___y_1119_ = stack[11].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1108_, v_baseMonadInfo_1109_, v_casesOnWrapper_1110_, v_restoreCont_1111_, v_dec_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object* v_getCont_1148_, lean_object* v_baseMonadInfo_1149_, lean_object* v_casesOnWrapper_1150_, lean_object* v_restoreCont_1151_, lean_object* v_dec_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1148_, v_baseMonadInfo_1149_, v_casesOnWrapper_1150_, v_restoreCont_1151_, v_dec_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1161_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object* v_baseMonadInfo_1162_, lean_object* v_stM_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1162_, v___y_1164_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc_ref(v___y_1165_);
v___x_1174_ = lean_apply_9(v_stM_1163_, v___x_1173_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, lean_box(0));
return v___x_1174_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseMonadInfo_1162_ = stack[0].m_obj;
lean_object* v_stM_1163_ = stack[1].m_obj;
lean_object* v___y_1164_ = stack[2].m_obj;
lean_object* v___y_1165_ = stack[3].m_obj;
lean_object* v___y_1166_ = stack[4].m_obj;
lean_object* v___y_1167_ = stack[5].m_obj;
lean_object* v___y_1168_ = stack[6].m_obj;
lean_object* v___y_1169_ = stack[7].m_obj;
lean_object* v___y_1170_ = stack[8].m_obj;
lean_object* v___y_1171_ = stack[9].m_obj;
lean_object* v_res_1175_;
v_res_1175_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1162_, v_stM_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
stack->m_obj
 = v_res_1175_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object* v_baseMonadInfo_1176_, lean_object* v_stM_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1176_, v_stM_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_baseMonadInfo_1176_);
return v_res_1187_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object* v_m_1188_, lean_object* v_baseMonadInfo_1189_, lean_object* v_optionTWrapper_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
lean_inc_ref(v___y_1191_);
v___x_1199_ = lean_apply_8(v_m_1188_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, lean_box(0));
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1214_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_u_1204_; lean_object* v_v_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v_u_1204_ = lean_ctor_get(v_baseMonadInfo_1189_, 1);
v_v_1205_ = lean_ctor_get(v_baseMonadInfo_1189_, 2);
v___x_1206_ = lean_box(0);
lean_inc(v_v_1205_);
v___x_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_v_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
lean_inc(v_u_1204_);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_u_1204_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_mkConst(v_optionTWrapper_1190_, v___x_1208_);
v___x_1210_ = l_Lean_Expr_app___override(v___x_1209_, v_a_1200_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1210_);
v___x_1212_ = v___x_1202_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_dec(v_optionTWrapper_1190_);
return v___x_1199_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_optionT___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1188_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_1189_ = stack[1].m_obj;
lean_object* v_optionTWrapper_1190_ = stack[2].m_obj;
lean_object* v___y_1191_ = stack[3].m_obj;
lean_object* v___y_1192_ = stack[4].m_obj;
lean_object* v___y_1193_ = stack[5].m_obj;
lean_object* v___y_1194_ = stack[6].m_obj;
lean_object* v___y_1195_ = stack[7].m_obj;
lean_object* v___y_1196_ = stack[8].m_obj;
lean_object* v___y_1197_ = stack[9].m_obj;
lean_object* v_res_1215_;
v_res_1215_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1188_, v_baseMonadInfo_1189_, v_optionTWrapper_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
stack->m_obj
 = v_res_1215_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object* v_m_1216_, lean_object* v_baseMonadInfo_1217_, lean_object* v_optionTWrapper_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1216_, v_baseMonadInfo_1217_, v_optionTWrapper_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_baseMonadInfo_1217_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object* v_baseMonadInfo_1228_, lean_object* v_optionTWrapper_1229_, lean_object* v_casesOnWrapper_1230_, lean_object* v_getCont_1231_, lean_object* v_base_1232_){
_start:
{
lean_object* v_description_1233_; lean_object* v_m_1234_; lean_object* v_stM_1235_; lean_object* v_runInBase_1236_; lean_object* v_restoreCont_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1249_; 
v_description_1233_ = lean_ctor_get(v_base_1232_, 0);
v_m_1234_ = lean_ctor_get(v_base_1232_, 1);
v_stM_1235_ = lean_ctor_get(v_base_1232_, 2);
v_runInBase_1236_ = lean_ctor_get(v_base_1232_, 3);
v_restoreCont_1237_ = lean_ctor_get(v_base_1232_, 4);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_base_1232_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1239_ = v_base_1232_;
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_restoreCont_1237_);
lean_inc(v_runInBase_1236_);
lean_inc(v_stM_1235_);
lean_inc(v_m_1234_);
lean_inc(v_description_1233_);
lean_dec(v_base_1232_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___x_1247_; 
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1241_, 0, v_runInBase_1236_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1), 2, 1);
lean_closure_set(v___f_1242_, 0, v_description_1233_);
lean_inc_ref_n(v_baseMonadInfo_1228_, 2);
v___f_1243_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed), 13, 4);
lean_closure_set(v___f_1243_, 0, v_getCont_1231_);
lean_closure_set(v___f_1243_, 1, v_baseMonadInfo_1228_);
lean_closure_set(v___f_1243_, 2, v_casesOnWrapper_1230_);
lean_closure_set(v___f_1243_, 3, v_restoreCont_1237_);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed), 11, 2);
lean_closure_set(v___f_1244_, 0, v_baseMonadInfo_1228_);
lean_closure_set(v___f_1244_, 1, v_stM_1235_);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed), 11, 3);
lean_closure_set(v___f_1245_, 0, v_m_1234_);
lean_closure_set(v___f_1245_, 1, v_baseMonadInfo_1228_);
lean_closure_set(v___f_1245_, 2, v_optionTWrapper_1229_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 4, v___f_1243_);
lean_ctor_set(v___x_1239_, 3, v___f_1241_);
lean_ctor_set(v___x_1239_, 2, v___f_1244_);
lean_ctor_set(v___x_1239_, 1, v___f_1245_);
lean_ctor_set(v___x_1239_, 0, v___f_1242_);
v___x_1247_ = v___x_1239_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___f_1245_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v___f_1244_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v___f_1241_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v___f_1243_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object* v_00_u03b1_1250_, lean_object* v_name_1251_, uint8_t v_bi_1252_, lean_object* v_type_1253_, lean_object* v_k_1254_, uint8_t v_kind_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_1251_, v_bi_1252_, v_type_1253_, v_k_1254_, v_kind_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1251_ = stack[1].m_obj;
uint8_t v_bi_1252_ = stack[2].m_num;
lean_object* v_type_1253_ = stack[3].m_obj;
lean_object* v_k_1254_ = stack[4].m_obj;
uint8_t v_kind_1255_ = stack[5].m_num;
lean_object* v___y_1256_ = stack[6].m_obj;
lean_object* v___y_1257_ = stack[7].m_obj;
lean_object* v___y_1258_ = stack[8].m_obj;
lean_object* v___y_1259_ = stack[9].m_obj;
lean_object* v___y_1260_ = stack[10].m_obj;
lean_object* v___y_1261_ = stack[11].m_obj;
lean_object* v___y_1262_ = stack[12].m_obj;
lean_object* v_res_1265_;
v_res_1265_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_box(0), v_name_1251_, v_bi_1252_, v_type_1253_, v_k_1254_, v_kind_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_name_1267_, lean_object* v_bi_1268_, lean_object* v_type_1269_, lean_object* v_k_1270_, lean_object* v_kind_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v_bi_boxed_1280_; uint8_t v_kind_boxed_1281_; lean_object* v_res_1282_; 
v_bi_boxed_1280_ = lean_unbox(v_bi_1268_);
v_kind_boxed_1281_ = lean_unbox(v_kind_1271_);
v_res_1282_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_1266_, v_name_1267_, v_bi_boxed_1280_, v_type_1269_, v_k_1270_, v_kind_boxed_1281_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1282_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object* v_00_u03b1_1283_, lean_object* v_name_1284_, lean_object* v_type_1285_, lean_object* v_k_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1284_, v_type_1285_, v_k_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1284_ = stack[1].m_obj;
lean_object* v_type_1285_ = stack[2].m_obj;
lean_object* v_k_1286_ = stack[3].m_obj;
lean_object* v___y_1287_ = stack[4].m_obj;
lean_object* v___y_1288_ = stack[5].m_obj;
lean_object* v___y_1289_ = stack[6].m_obj;
lean_object* v___y_1290_ = stack[7].m_obj;
lean_object* v___y_1291_ = stack[8].m_obj;
lean_object* v___y_1292_ = stack[9].m_obj;
lean_object* v___y_1293_ = stack[10].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_box(0), v_name_1284_, v_type_1285_, v_k_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_name_1298_, lean_object* v_type_1299_, lean_object* v_k_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(v_00_u03b1_1297_, v_name_1298_, v_type_1299_, v_k_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1309_;
}
}
lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object* v_baseMonadInfo_1313_, lean_object* v_getCont_1314_, lean_object* v_00_u03b1_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; 
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc_ref(v_a_1317_);
lean_inc_ref(v_a_1316_);
v___x_1324_ = lean_apply_8(v_getCont_1314_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, lean_box(0));
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1347_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1347_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1347_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_u_1329_; lean_object* v_resultType_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1345_; 
v_u_1329_ = lean_ctor_get(v_baseMonadInfo_1313_, 1);
v_resultType_1330_ = lean_ctor_get(v_a_1325_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_a_1325_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_a_1325_, 1);
lean_dec(v_unused_1346_);
v___x_1332_ = v_a_1325_;
v_isShared_1333_ = v_isSharedCheck_1345_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_resultType_1330_);
lean_dec(v_a_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1345_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_box(0);
lean_inc(v_u_1329_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set_tag(v___x_1332_, 1);
lean_ctor_set(v___x_1332_, 1, v___x_1334_);
lean_ctor_set(v___x_1332_, 0, v_u_1329_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_u_1329_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
lean_inc(v_u_1329_);
v___x_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_u_1329_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
v___x_1339_ = l_Lean_mkConst(v___x_1337_, v___x_1338_);
v___x_1340_ = l_Lean_mkAppB(v___x_1339_, v_resultType_1330_, v_00_u03b1_1315_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1340_);
v___x_1342_ = v___x_1327_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v_00_u03b1_1315_);
v_a_1348_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1324_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1324_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseMonadInfo_1313_ = stack[0].m_obj;
lean_object* v_getCont_1314_ = stack[1].m_obj;
lean_object* v_00_u03b1_1315_ = stack[2].m_obj;
lean_object* v_a_1316_ = stack[3].m_obj;
lean_object* v_a_1317_ = stack[4].m_obj;
lean_object* v_a_1318_ = stack[5].m_obj;
lean_object* v_a_1319_ = stack[6].m_obj;
lean_object* v_a_1320_ = stack[7].m_obj;
lean_object* v_a_1321_ = stack[8].m_obj;
lean_object* v_a_1322_ = stack[9].m_obj;
lean_object* v_res_1356_;
v_res_1356_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1313_, v_getCont_1314_, v_00_u03b1_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
stack->m_obj
 = v_res_1356_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object* v_baseMonadInfo_1357_, lean_object* v_getCont_1358_, lean_object* v_00_u03b1_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1357_, v_getCont_1358_, v_00_u03b1_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec_ref(v_baseMonadInfo_1357_);
return v_res_1368_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object* v_dec_1369_, lean_object* v_r_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_k_1379_; lean_object* v___x_1380_; 
v_k_1379_ = lean_ctor_get(v_dec_1369_, 2);
lean_inc_ref(v_k_1379_);
lean_dec_ref(v_dec_1369_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc_ref(v___y_1371_);
v___x_1380_ = lean_apply_8(v_k_1379_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; uint8_t v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_n(v_a_1381_, 2);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_mk_empty_array_with_capacity(v___x_1382_);
v___x_1384_ = lean_array_push(v___x_1383_, v_r_1370_);
v___x_1385_ = 0;
v___x_1386_ = 1;
v___x_1387_ = 1;
v___x_1388_ = l_Lean_Meta_mkLambdaFVars(v___x_1384_, v_a_1381_, v___x_1385_, v___x_1386_, v___x_1385_, v___x_1386_, v___x_1387_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec_ref(v___x_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
v___x_1390_ = lean_infer_type(v_a_1381_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1399_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_a_1389_);
lean_ctor_set(v___x_1395_, 1, v_a_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1389_);
v_a_1400_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1390_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1390_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_a_1381_);
v_a_1408_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1388_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1388_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_r_1370_);
v_a_1416_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1380_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1380_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_dec_1369_ = stack[0].m_obj;
lean_object* v_r_1370_ = stack[1].m_obj;
lean_object* v___y_1371_ = stack[2].m_obj;
lean_object* v___y_1372_ = stack[3].m_obj;
lean_object* v___y_1373_ = stack[4].m_obj;
lean_object* v___y_1374_ = stack[5].m_obj;
lean_object* v___y_1375_ = stack[6].m_obj;
lean_object* v___y_1376_ = stack[7].m_obj;
lean_object* v___y_1377_ = stack[8].m_obj;
lean_object* v_res_1424_;
v_res_1424_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_dec_1369_, v_r_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
stack->m_obj
 = v_res_1424_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object* v_dec_1425_, lean_object* v_r_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_dec_1425_, v_r_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1435_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object* v_a_1436_, lean_object* v_r_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_k_1446_; lean_object* v___x_1447_; 
v_k_1446_ = lean_ctor_get(v_a_1436_, 1);
lean_inc_ref(v_k_1446_);
lean_dec_ref(v_a_1436_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc_ref(v_r_1437_);
v___x_1447_ = lean_apply_9(v_k_1446_, v_r_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, lean_box(0));
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; uint8_t v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_mk_empty_array_with_capacity(v___x_1449_);
v___x_1451_ = lean_array_push(v___x_1450_, v_r_1437_);
v___x_1452_ = 0;
v___x_1453_ = 1;
v___x_1454_ = 1;
v___x_1455_ = l_Lean_Meta_mkLambdaFVars(v___x_1451_, v_a_1448_, v___x_1452_, v___x_1453_, v___x_1452_, v___x_1453_, v___x_1454_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec_ref(v___x_1451_);
return v___x_1455_;
}
else
{
lean_dec_ref(v_r_1437_);
return v___x_1447_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1436_ = stack[0].m_obj;
lean_object* v_r_1437_ = stack[1].m_obj;
lean_object* v___y_1438_ = stack[2].m_obj;
lean_object* v___y_1439_ = stack[3].m_obj;
lean_object* v___y_1440_ = stack[4].m_obj;
lean_object* v___y_1441_ = stack[5].m_obj;
lean_object* v___y_1442_ = stack[6].m_obj;
lean_object* v___y_1443_ = stack[7].m_obj;
lean_object* v___y_1444_ = stack[8].m_obj;
lean_object* v_res_1456_;
v_res_1456_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_a_1436_, v_r_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
stack->m_obj
 = v_res_1456_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object* v_a_1457_, lean_object* v_r_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_a_1457_, v_r_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1467_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object* v_a_1468_, lean_object* v_getCont_1469_, lean_object* v_resultName_1470_, lean_object* v_resultType_1471_, lean_object* v___f_1472_, lean_object* v_baseMonadInfo_1473_, lean_object* v_casesOnWrapper_1474_, lean_object* v_00_u03b5_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Meta_getFVarFromUserName(v_a_1468_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc_ref(v___y_1476_);
v___x_1486_ = lean_apply_8(v_getCont_1469_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, lean_box(0));
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_n(v_a_1487_, 2);
lean_dec_ref_known(v___x_1486_, 1);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1488_, 0, v_a_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1490_ = l_Lean_Core_mkFreshUserName(v___x_1489_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_resultType_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1532_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v_resultType_1492_ = lean_ctor_get(v_a_1487_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_a_1487_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v_a_1487_, 1);
lean_dec(v_unused_1533_);
v___x_1494_ = v_a_1487_;
v_isShared_1495_ = v_isSharedCheck_1532_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_resultType_1492_);
lean_dec(v_a_1487_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1532_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1491_, v_resultType_1492_, v___f_1488_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
lean_inc_ref(v_resultType_1471_);
v___x_1498_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1470_, v_resultType_1471_, v___f_1472_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1523_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1522_; 
v_fst_1503_ = lean_ctor_get(v_a_1499_, 0);
v_snd_1504_ = lean_ctor_get(v_a_1499_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_a_1499_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1506_ = v_a_1499_;
v_isShared_1507_ = v_isSharedCheck_1522_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_snd_1504_);
lean_inc(v_fst_1503_);
lean_dec(v_a_1499_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1522_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_u_1508_; lean_object* v_v_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_u_1508_ = lean_ctor_get(v_baseMonadInfo_1473_, 1);
v_v_1509_ = lean_ctor_get(v_baseMonadInfo_1473_, 2);
v___x_1510_ = lean_box(0);
lean_inc(v_v_1509_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 1);
lean_ctor_set(v___x_1506_, 1, v___x_1510_);
lean_ctor_set(v___x_1506_, 0, v_v_1509_);
v___x_1512_ = v___x_1506_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_v_1509_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
lean_inc(v_u_1508_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 1);
lean_ctor_set(v___x_1494_, 1, v___x_1512_);
lean_ctor_set(v___x_1494_, 0, v_u_1508_);
v___x_1514_ = v___x_1494_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_u_1508_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1515_ = l_Lean_mkConst(v_casesOnWrapper_1474_, v___x_1514_);
v___x_1516_ = l_Lean_mkApp6(v___x_1515_, v_00_u03b5_1475_, v_resultType_1471_, v_snd_1504_, v_a_1485_, v_a_1497_, v_fst_1503_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1516_);
v___x_1518_ = v___x_1501_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_a_1497_);
lean_del_object(v___x_1494_);
lean_dec(v_a_1485_);
lean_dec_ref(v_00_u03b5_1475_);
lean_dec(v_casesOnWrapper_1474_);
lean_dec_ref(v_resultType_1471_);
v_a_1524_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1498_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1498_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_del_object(v___x_1494_);
lean_dec(v_a_1485_);
lean_dec_ref(v_00_u03b5_1475_);
lean_dec(v_casesOnWrapper_1474_);
lean_dec_ref(v___f_1472_);
lean_dec_ref(v_resultType_1471_);
lean_dec(v_resultName_1470_);
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v___f_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1485_);
lean_dec_ref(v_00_u03b5_1475_);
lean_dec(v_casesOnWrapper_1474_);
lean_dec_ref(v___f_1472_);
lean_dec_ref(v_resultType_1471_);
lean_dec(v_resultName_1470_);
v_a_1534_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1490_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1490_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1485_);
lean_dec_ref(v_00_u03b5_1475_);
lean_dec(v_casesOnWrapper_1474_);
lean_dec_ref(v___f_1472_);
lean_dec_ref(v_resultType_1471_);
lean_dec(v_resultName_1470_);
v_a_1542_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1486_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1486_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1475_);
lean_dec(v_casesOnWrapper_1474_);
lean_dec_ref(v___f_1472_);
lean_dec_ref(v_resultType_1471_);
lean_dec(v_resultName_1470_);
lean_dec_ref(v_getCont_1469_);
return v___x_1484_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1468_ = stack[0].m_obj;
lean_object* v_getCont_1469_ = stack[1].m_obj;
lean_object* v_resultName_1470_ = stack[2].m_obj;
lean_object* v_resultType_1471_ = stack[3].m_obj;
lean_object* v___f_1472_ = stack[4].m_obj;
lean_object* v_baseMonadInfo_1473_ = stack[5].m_obj;
lean_object* v_casesOnWrapper_1474_ = stack[6].m_obj;
lean_object* v_00_u03b5_1475_ = stack[7].m_obj;
lean_object* v___y_1476_ = stack[8].m_obj;
lean_object* v___y_1477_ = stack[9].m_obj;
lean_object* v___y_1478_ = stack[10].m_obj;
lean_object* v___y_1479_ = stack[11].m_obj;
lean_object* v___y_1480_ = stack[12].m_obj;
lean_object* v___y_1481_ = stack[13].m_obj;
lean_object* v___y_1482_ = stack[14].m_obj;
lean_object* v_res_1550_;
v_res_1550_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1468_, v_getCont_1469_, v_resultName_1470_, v_resultType_1471_, v___f_1472_, v_baseMonadInfo_1473_, v_casesOnWrapper_1474_, v_00_u03b5_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
stack->m_obj
 = v_res_1550_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object* v_a_1551_, lean_object* v_getCont_1552_, lean_object* v_resultName_1553_, lean_object* v_resultType_1554_, lean_object* v___f_1555_, lean_object* v_baseMonadInfo_1556_, lean_object* v_casesOnWrapper_1557_, lean_object* v_00_u03b5_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1551_, v_getCont_1552_, v_resultName_1553_, v_resultType_1554_, v___f_1555_, v_baseMonadInfo_1556_, v_casesOnWrapper_1557_, v_00_u03b5_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v_baseMonadInfo_1556_);
return v_res_1567_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object* v_getCont_1568_, lean_object* v_baseMonadInfo_1569_, lean_object* v_casesOnWrapper_1570_, lean_object* v_00_u03b5_1571_, lean_object* v_restoreCont_1572_, lean_object* v_dec_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_inc_ref(v_dec_1573_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1582_, 0, v_dec_1573_);
v___x_1583_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1584_ = l_Lean_Core_mkFreshUserName(v___x_1583_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_resultName_1586_; lean_object* v_resultType_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1607_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_resultName_1586_ = lean_ctor_get(v_dec_1573_, 0);
v_resultType_1587_ = lean_ctor_get(v_dec_1573_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_dec_1573_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_dec_1573_, 2);
lean_dec(v_unused_1608_);
v___x_1589_ = v_dec_1573_;
v_isShared_1590_ = v_isSharedCheck_1607_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_resultType_1587_);
lean_inc(v_resultName_1586_);
lean_dec(v_dec_1573_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1607_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___f_1591_; lean_object* v___x_1592_; 
lean_inc_ref(v_baseMonadInfo_1569_);
lean_inc_ref(v_resultType_1587_);
lean_inc_ref(v_getCont_1568_);
lean_inc(v_a_1585_);
v___f_1591_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed), 16, 8);
lean_closure_set(v___f_1591_, 0, v_a_1585_);
lean_closure_set(v___f_1591_, 1, v_getCont_1568_);
lean_closure_set(v___f_1591_, 2, v_resultName_1586_);
lean_closure_set(v___f_1591_, 3, v_resultType_1587_);
lean_closure_set(v___f_1591_, 4, v___f_1582_);
lean_closure_set(v___f_1591_, 5, v_baseMonadInfo_1569_);
lean_closure_set(v___f_1591_, 6, v_casesOnWrapper_1570_);
lean_closure_set(v___f_1591_, 7, v_00_u03b5_1571_);
v___x_1592_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1569_, v_getCont_1568_, v_resultType_1587_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec_ref(v_baseMonadInfo_1569_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; uint8_t v___x_1594_; lean_object* v___x_1596_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = 0;
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 2, v___f_1591_);
lean_ctor_set(v___x_1589_, 1, v_a_1593_);
lean_ctor_set(v___x_1589_, 0, v_a_1585_);
v___x_1596_ = v___x_1589_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1585_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1593_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v___f_1591_);
v___x_1596_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*3, v___x_1594_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
lean_inc(v___y_1576_);
lean_inc_ref(v___y_1575_);
lean_inc_ref(v___y_1574_);
v___x_1597_ = lean_apply_9(v_restoreCont_1572_, v___x_1596_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, lean_box(0));
return v___x_1597_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v___f_1591_);
lean_del_object(v___x_1589_);
lean_dec(v_a_1585_);
lean_dec_ref(v_restoreCont_1572_);
v_a_1599_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1592_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1592_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v___f_1582_);
lean_dec_ref(v_dec_1573_);
lean_dec_ref(v_restoreCont_1572_);
lean_dec_ref(v_00_u03b5_1571_);
lean_dec(v_casesOnWrapper_1570_);
lean_dec_ref(v_baseMonadInfo_1569_);
lean_dec_ref(v_getCont_1568_);
v_a_1609_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1584_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1584_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_getCont_1568_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_1569_ = stack[1].m_obj;
lean_object* v_casesOnWrapper_1570_ = stack[2].m_obj;
lean_object* v_00_u03b5_1571_ = stack[3].m_obj;
lean_object* v_restoreCont_1572_ = stack[4].m_obj;
lean_object* v_dec_1573_ = stack[5].m_obj;
lean_object* v___y_1574_ = stack[6].m_obj;
lean_object* v___y_1575_ = stack[7].m_obj;
lean_object* v___y_1576_ = stack[8].m_obj;
lean_object* v___y_1577_ = stack[9].m_obj;
lean_object* v___y_1578_ = stack[10].m_obj;
lean_object* v___y_1579_ = stack[11].m_obj;
lean_object* v___y_1580_ = stack[12].m_obj;
lean_object* v_res_1617_;
v_res_1617_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_getCont_1568_, v_baseMonadInfo_1569_, v_casesOnWrapper_1570_, v_00_u03b5_1571_, v_restoreCont_1572_, v_dec_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
stack->m_obj
 = v_res_1617_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object* v_getCont_1618_, lean_object* v_baseMonadInfo_1619_, lean_object* v_casesOnWrapper_1620_, lean_object* v_00_u03b5_1621_, lean_object* v_restoreCont_1622_, lean_object* v_dec_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_getCont_1618_, v_baseMonadInfo_1619_, v_casesOnWrapper_1620_, v_00_u03b5_1621_, v_restoreCont_1622_, v_dec_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1632_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object* v_00_u03b5_1639_, lean_object* v_description_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1);
v___x_1643_ = l_Lean_MessageData_ofExpr(v_00_u03b5_1639_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_apply_1(v_description_1640_, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1646_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
return v___x_1649_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object* v_baseMonadInfo_1650_, lean_object* v_getCont_1651_, lean_object* v_stM_1652_, lean_object* v_00_u03b1_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1650_, v_getCont_1651_, v_00_u03b1_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc_ref(v___y_1654_);
v___x_1664_ = lean_apply_9(v_stM_1652_, v_a_1663_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1664_;
}
else
{
lean_dec_ref(v_stM_1652_);
return v___x_1662_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseMonadInfo_1650_ = stack[0].m_obj;
lean_object* v_getCont_1651_ = stack[1].m_obj;
lean_object* v_stM_1652_ = stack[2].m_obj;
lean_object* v_00_u03b1_1653_ = stack[3].m_obj;
lean_object* v___y_1654_ = stack[4].m_obj;
lean_object* v___y_1655_ = stack[5].m_obj;
lean_object* v___y_1656_ = stack[6].m_obj;
lean_object* v___y_1657_ = stack[7].m_obj;
lean_object* v___y_1658_ = stack[8].m_obj;
lean_object* v___y_1659_ = stack[9].m_obj;
lean_object* v___y_1660_ = stack[10].m_obj;
lean_object* v_res_1665_;
v_res_1665_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1650_, v_getCont_1651_, v_stM_1652_, v_00_u03b1_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
stack->m_obj
 = v_res_1665_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object* v_baseMonadInfo_1666_, lean_object* v_getCont_1667_, lean_object* v_stM_1668_, lean_object* v_00_u03b1_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1666_, v_getCont_1667_, v_stM_1668_, v_00_u03b1_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec_ref(v_baseMonadInfo_1666_);
return v_res_1678_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object* v_runInBase_1683_, lean_object* v_e_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1));
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_mk_empty_array_with_capacity(v___x_1694_);
v___x_1696_ = lean_array_push(v___x_1695_, v_e_1684_);
v___x_1697_ = l_Lean_Meta_mkAppM(v___x_1693_, v___x_1696_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc_ref(v___y_1685_);
v___x_1699_ = lean_apply_9(v_runInBase_1683_, v_a_1698_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, lean_box(0));
return v___x_1699_;
}
else
{
lean_dec_ref(v_runInBase_1683_);
return v___x_1697_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_runInBase_1683_ = stack[0].m_obj;
lean_object* v_e_1684_ = stack[1].m_obj;
lean_object* v___y_1685_ = stack[2].m_obj;
lean_object* v___y_1686_ = stack[3].m_obj;
lean_object* v___y_1687_ = stack[4].m_obj;
lean_object* v___y_1688_ = stack[5].m_obj;
lean_object* v___y_1689_ = stack[6].m_obj;
lean_object* v___y_1690_ = stack[7].m_obj;
lean_object* v___y_1691_ = stack[8].m_obj;
lean_object* v_res_1700_;
v_res_1700_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1683_, v_e_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object* v_runInBase_1701_, lean_object* v_e_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1701_, v_e_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1711_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object* v_m_1712_, lean_object* v_baseMonadInfo_1713_, lean_object* v_exceptTWrapper_1714_, lean_object* v_00_u03b5_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc_ref(v___y_1716_);
v___x_1724_ = lean_apply_8(v_m_1712_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, lean_box(0));
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1739_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1739_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1739_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_u_1729_; lean_object* v_v_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v_u_1729_ = lean_ctor_get(v_baseMonadInfo_1713_, 1);
v_v_1730_ = lean_ctor_get(v_baseMonadInfo_1713_, 2);
v___x_1731_ = lean_box(0);
lean_inc(v_v_1730_);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_v_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
lean_inc(v_u_1729_);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_u_1729_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_mkConst(v_exceptTWrapper_1714_, v___x_1733_);
v___x_1735_ = l_Lean_mkAppB(v___x_1734_, v_00_u03b5_1715_, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1735_);
v___x_1737_ = v___x_1727_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1715_);
lean_dec(v_exceptTWrapper_1714_);
return v___x_1724_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_exceptT___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1712_ = stack[0].m_obj;
lean_object* v_baseMonadInfo_1713_ = stack[1].m_obj;
lean_object* v_exceptTWrapper_1714_ = stack[2].m_obj;
lean_object* v_00_u03b5_1715_ = stack[3].m_obj;
lean_object* v___y_1716_ = stack[4].m_obj;
lean_object* v___y_1717_ = stack[5].m_obj;
lean_object* v___y_1718_ = stack[6].m_obj;
lean_object* v___y_1719_ = stack[7].m_obj;
lean_object* v___y_1720_ = stack[8].m_obj;
lean_object* v___y_1721_ = stack[9].m_obj;
lean_object* v___y_1722_ = stack[10].m_obj;
lean_object* v_res_1740_;
v_res_1740_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1712_, v_baseMonadInfo_1713_, v_exceptTWrapper_1714_, v_00_u03b5_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
stack->m_obj
 = v_res_1740_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object* v_m_1741_, lean_object* v_baseMonadInfo_1742_, lean_object* v_exceptTWrapper_1743_, lean_object* v_00_u03b5_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1741_, v_baseMonadInfo_1742_, v_exceptTWrapper_1743_, v_00_u03b5_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v_baseMonadInfo_1742_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object* v_baseMonadInfo_1754_, lean_object* v_exceptTWrapper_1755_, lean_object* v_casesOnWrapper_1756_, lean_object* v_getCont_1757_, lean_object* v_00_u03b5_1758_, lean_object* v_base_1759_){
_start:
{
lean_object* v_description_1760_; lean_object* v_m_1761_; lean_object* v_stM_1762_; lean_object* v_runInBase_1763_; lean_object* v_restoreCont_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1776_; 
v_description_1760_ = lean_ctor_get(v_base_1759_, 0);
v_m_1761_ = lean_ctor_get(v_base_1759_, 1);
v_stM_1762_ = lean_ctor_get(v_base_1759_, 2);
v_runInBase_1763_ = lean_ctor_get(v_base_1759_, 3);
v_restoreCont_1764_ = lean_ctor_get(v_base_1759_, 4);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_base_1759_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1766_ = v_base_1759_;
v_isShared_1767_ = v_isSharedCheck_1776_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_restoreCont_1764_);
lean_inc(v_runInBase_1763_);
lean_inc(v_stM_1762_);
lean_inc(v_m_1761_);
lean_inc(v_description_1760_);
lean_dec(v_base_1759_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1776_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___f_1768_; lean_object* v___f_1769_; lean_object* v___f_1770_; lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___x_1774_; 
lean_inc_ref_n(v_00_u03b5_1758_, 2);
lean_inc_ref_n(v_baseMonadInfo_1754_, 2);
lean_inc_ref(v_getCont_1757_);
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed), 14, 5);
lean_closure_set(v___f_1768_, 0, v_getCont_1757_);
lean_closure_set(v___f_1768_, 1, v_baseMonadInfo_1754_);
lean_closure_set(v___f_1768_, 2, v_casesOnWrapper_1756_);
lean_closure_set(v___f_1768_, 3, v_00_u03b5_1758_);
lean_closure_set(v___f_1768_, 4, v_restoreCont_1764_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4), 3, 2);
lean_closure_set(v___f_1769_, 0, v_00_u03b5_1758_);
lean_closure_set(v___f_1769_, 1, v_description_1760_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed), 12, 3);
lean_closure_set(v___f_1770_, 0, v_baseMonadInfo_1754_);
lean_closure_set(v___f_1770_, 1, v_getCont_1757_);
lean_closure_set(v___f_1770_, 2, v_stM_1762_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed), 10, 1);
lean_closure_set(v___f_1771_, 0, v_runInBase_1763_);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed), 12, 4);
lean_closure_set(v___f_1772_, 0, v_m_1761_);
lean_closure_set(v___f_1772_, 1, v_baseMonadInfo_1754_);
lean_closure_set(v___f_1772_, 2, v_exceptTWrapper_1755_);
lean_closure_set(v___f_1772_, 3, v_00_u03b5_1758_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 4, v___f_1768_);
lean_ctor_set(v___x_1766_, 3, v___f_1771_);
lean_ctor_set(v___x_1766_, 2, v___f_1770_);
lean_ctor_set(v___x_1766_, 1, v___f_1772_);
lean_ctor_set(v___x_1766_, 0, v___f_1769_);
v___x_1774_ = v___x_1766_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___f_1769_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___f_1772_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v___f_1770_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v___f_1771_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v___f_1768_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object* v_baseMonadInfo_1786_, lean_object* v_00_u03c1_1787_, lean_object* v_m_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1));
v___x_1790_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4));
v___x_1791_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5));
v___x_1792_ = l_Lean_Elab_Do_ControlStack_exceptT(v_baseMonadInfo_1786_, v___x_1789_, v___x_1790_, v___x_1791_, v_00_u03c1_1787_, v_m_1788_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_1796_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
if (lean_obj_tag(v_a_1805_) == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1807_);
v___x_1809_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1);
v___x_1810_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1809_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
return v___x_1810_;
}
else
{
lean_object* v_val_1811_; lean_object* v___x_1813_; 
v_val_1811_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_val_1811_);
lean_dec_ref_known(v_a_1805_, 1);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_val_1811_);
v___x_1813_ = v___x_1807_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_val_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1804_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1804_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_breakT___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1796_ = stack[0].m_obj;
lean_object* v___y_1797_ = stack[1].m_obj;
lean_object* v___y_1798_ = stack[2].m_obj;
lean_object* v___y_1799_ = stack[3].m_obj;
lean_object* v___y_1800_ = stack[4].m_obj;
lean_object* v___y_1801_ = stack[5].m_obj;
lean_object* v___y_1802_ = stack[6].m_obj;
lean_object* v_res_1824_;
v_res_1824_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
stack->m_obj
 = v_res_1824_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object* v_baseMonadInfo_1842_, lean_object* v_m_1843_){
_start:
{
lean_object* v_getCont_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_getCont_1844_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__0));
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__2));
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__4));
v___x_1847_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1842_, v___x_1845_, v___x_1846_, v_getCont_1844_, v_m_1843_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_1851_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1870_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
if (lean_obj_tag(v_a_1860_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_del_object(v___x_1862_);
v___x_1864_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1);
v___x_1865_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1864_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1865_;
}
else
{
lean_object* v_val_1866_; lean_object* v___x_1868_; 
v_val_1866_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_a_1860_, 1);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_val_1866_);
v___x_1868_ = v___x_1862_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_val_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_a_1871_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1859_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1859_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_continueT___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1851_ = stack[0].m_obj;
lean_object* v___y_1852_ = stack[1].m_obj;
lean_object* v___y_1853_ = stack[2].m_obj;
lean_object* v___y_1854_ = stack[3].m_obj;
lean_object* v___y_1855_ = stack[4].m_obj;
lean_object* v___y_1856_ = stack[5].m_obj;
lean_object* v___y_1857_ = stack[6].m_obj;
lean_object* v_res_1879_;
v_res_1879_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
stack->m_obj
 = v_res_1879_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object* v_baseMonadInfo_1897_, lean_object* v_m_1898_){
_start:
{
lean_object* v_getCont_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_getCont_1899_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__0));
v___x_1900_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__2));
v___x_1901_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__4));
v___x_1902_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1897_, v___x_1900_, v___x_1901_, v_getCont_1899_, v_m_1898_);
return v___x_1902_;
}
}
lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object* v_mi_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_m_1914_; lean_object* v_u_1915_; lean_object* v_v_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_m_1914_ = lean_ctor_get(v_mi_1906_, 0);
lean_inc_ref(v_m_1914_);
v_u_1915_ = lean_ctor_get(v_mi_1906_, 1);
lean_inc(v_u_1915_);
v_v_1916_ = lean_ctor_get(v_mi_1906_, 2);
lean_inc(v_v_1916_);
lean_dec_ref(v_mi_1906_);
v___x_1917_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1));
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_v_1916_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_u_1915_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_mkConst(v___x_1917_, v___x_1920_);
v___x_1922_ = l_Lean_Expr_app___override(v___x_1921_, v_m_1914_);
v___x_1923_ = lean_box(0);
v___x_1924_ = l_Lean_Elab_Term_mkInstMVar(v___x_1922_, v___x_1923_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1924_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad_0interp(lean_interpreter_value* stack)
{
lean_object* v_mi_1906_ = stack[0].m_obj;
lean_object* v_a_1907_ = stack[1].m_obj;
lean_object* v_a_1908_ = stack[2].m_obj;
lean_object* v_a_1909_ = stack[3].m_obj;
lean_object* v_a_1910_ = stack[4].m_obj;
lean_object* v_a_1911_ = stack[5].m_obj;
lean_object* v_a_1912_ = stack[6].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object* v_mi_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
return v_res_1934_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2));
v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4));
v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
return v___x_1943_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6));
v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
return v___x_1946_;
}
}
lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object* v_msg_1947_, lean_object* v_expected_1948_, lean_object* v_actual_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; 
lean_inc_ref(v_actual_1949_);
lean_inc_ref(v_expected_1948_);
v___x_1955_ = l_Lean_Meta_isExprDefEq(v_expected_1948_, v_actual_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1979_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1979_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1979_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_unbox(v_a_1956_);
lean_dec(v_a_1956_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_del_object(v___x_1958_);
v___x_1961_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
v___x_1962_ = l_Lean_stringToMessageData(v_msg_1947_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = l_Lean_MessageData_ofExpr(v_expected_1948_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Lean_MessageData_ofExpr(v_actual_1949_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1973_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec_ref(v_actual_1949_);
lean_dec_ref(v_expected_1948_);
lean_dec_ref(v_msg_1947_);
v___x_1975_ = lean_box(0);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1975_);
v___x_1977_ = v___x_1958_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_actual_1949_);
lean_dec_ref(v_expected_1948_);
lean_dec_ref(v_msg_1947_);
v_a_1980_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1955_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1955_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1947_ = stack[0].m_obj;
lean_object* v_expected_1948_ = stack[1].m_obj;
lean_object* v_actual_1949_ = stack[2].m_obj;
lean_object* v_a_1950_ = stack[3].m_obj;
lean_object* v_a_1951_ = stack[4].m_obj;
lean_object* v_a_1952_ = stack[5].m_obj;
lean_object* v_a_1953_ = stack[6].m_obj;
lean_object* v_res_1988_;
v_res_1988_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1947_, v_expected_1948_, v_actual_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
stack->m_obj
 = v_res_1988_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object* v_msg_1989_, lean_object* v_expected_1990_, lean_object* v_actual_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1989_, v_expected_1990_, v_actual_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1997_;
}
}
lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object* v_msg_1998_, lean_object* v_expected_1999_, lean_object* v_actual_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1998_, v_expected_1999_, v_actual_2000_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1998_ = stack[0].m_obj;
lean_object* v_expected_1999_ = stack[1].m_obj;
lean_object* v_actual_2000_ = stack[2].m_obj;
lean_object* v_a_2001_ = stack[3].m_obj;
lean_object* v_a_2002_ = stack[4].m_obj;
lean_object* v_a_2003_ = stack[5].m_obj;
lean_object* v_a_2004_ = stack[6].m_obj;
lean_object* v_a_2005_ = stack[7].m_obj;
lean_object* v_a_2006_ = stack[8].m_obj;
lean_object* v_a_2007_ = stack[9].m_obj;
lean_object* v_res_2010_;
v_res_2010_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_1998_, v_expected_1999_, v_actual_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
stack->m_obj
 = v_res_2010_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object* v_msg_2011_, lean_object* v_expected_2012_, lean_object* v_actual_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_2011_, v_expected_2012_, v_actual_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec_ref(v_a_2014_);
return v_res_2022_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object* v_base_2028_, uint8_t v_hasContinue_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_m_2038_; lean_object* v_runInBase_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2097_; 
v_m_2038_ = lean_ctor_get(v_base_2028_, 1);
v_runInBase_2039_ = lean_ctor_get(v_base_2028_, 3);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_base_2028_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; lean_object* v_unused_2099_; lean_object* v_unused_2100_; 
v_unused_2098_ = lean_ctor_get(v_base_2028_, 4);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_base_2028_, 2);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_base_2028_, 0);
lean_dec(v_unused_2100_);
v___x_2041_ = v_base_2028_;
v_isShared_2042_ = v_isSharedCheck_2097_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_runInBase_2039_);
lean_inc(v_m_2038_);
lean_dec(v_base_2028_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2097_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; 
lean_inc(v_a_2036_);
lean_inc_ref(v_a_2035_);
lean_inc(v_a_2034_);
lean_inc_ref(v_a_2033_);
lean_inc(v_a_2032_);
lean_inc_ref(v_a_2031_);
lean_inc_ref(v_a_2030_);
v___x_2043_ = lean_apply_8(v_m_2038_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, lean_box(0));
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_monadInfo_2044_; lean_object* v_a_2045_; lean_object* v_doBlockResultType_2046_; lean_object* v_u_2047_; lean_object* v_v_2048_; lean_object* v_cachedPUnit_2049_; lean_object* v_cachedPUnitUnit_2050_; lean_object* v___x_2052_; 
v_monadInfo_2044_ = lean_ctor_get(v_a_2030_, 0);
v_a_2045_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_n(v_a_2045_, 2);
lean_dec_ref_known(v___x_2043_, 1);
v_doBlockResultType_2046_ = lean_ctor_get(v_a_2030_, 3);
v_u_2047_ = lean_ctor_get(v_monadInfo_2044_, 1);
v_v_2048_ = lean_ctor_get(v_monadInfo_2044_, 2);
v_cachedPUnit_2049_ = lean_ctor_get(v_monadInfo_2044_, 3);
v_cachedPUnitUnit_2050_ = lean_ctor_get(v_monadInfo_2044_, 4);
lean_inc_ref(v_cachedPUnitUnit_2050_);
lean_inc_ref(v_cachedPUnit_2049_);
lean_inc(v_v_2048_);
lean_inc(v_u_2047_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 4, v_cachedPUnitUnit_2050_);
lean_ctor_set(v___x_2041_, 3, v_cachedPUnit_2049_);
lean_ctor_set(v___x_2041_, 2, v_v_2048_);
lean_ctor_set(v___x_2041_, 1, v_u_2047_);
lean_ctor_set(v___x_2041_, 0, v_a_2045_);
v___x_2052_ = v___x_2041_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2045_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_u_2047_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2048_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_cachedPUnit_2049_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_cachedPUnitUnit_2050_);
v___x_2052_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2052_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2056_ = 0;
v___x_2057_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2055_, v___x_2056_, v_a_2030_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___y_2060_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
if (v_hasContinue_2029_ == 0)
{
v___y_2060_ = v_a_2058_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2091_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_2092_ = lean_box(0);
lean_inc(v_u_2047_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_u_2047_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = l_Lean_mkConst(v___x_2091_, v___x_2093_);
v___x_2095_ = l_Lean_Expr_app___override(v___x_2094_, v_a_2058_);
v___y_2060_ = v___x_2095_;
goto v___jp_2059_;
}
v___jp_2059_:
{
lean_object* v___x_2061_; 
lean_inc_ref(v_doBlockResultType_2046_);
v___x_2061_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2046_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1));
v___x_2064_ = lean_box(0);
lean_inc(v_v_2048_);
v___x_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_v_2048_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
lean_inc(v_u_2047_);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_u_2047_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_mkConst(v___x_2063_, v___x_2066_);
v___x_2068_ = l_Lean_mkApp3(v___x_2067_, v___y_2060_, v_a_2045_, v_a_2054_);
lean_inc(v_a_2036_);
lean_inc_ref(v_a_2035_);
lean_inc(v_a_2034_);
lean_inc_ref(v_a_2033_);
lean_inc(v_a_2032_);
lean_inc_ref(v_a_2031_);
lean_inc_ref(v_a_2030_);
v___x_2069_ = lean_apply_9(v_runInBase_2039_, v___x_2068_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, lean_box(0));
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc_n(v_a_2070_, 2);
lean_dec_ref_known(v___x_2069_, 1);
lean_inc(v_a_2036_);
lean_inc_ref(v_a_2035_);
lean_inc(v_a_2034_);
lean_inc_ref(v_a_2033_);
v___x_2071_ = lean_infer_type(v_a_2070_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2));
v___x_2074_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2073_, v_a_2062_, v_a_2072_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2074_, 0);
lean_dec(v_unused_2082_);
v___x_2076_ = v___x_2074_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v___x_2074_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v_a_2070_);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2070_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_2070_);
v_a_2083_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2074_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2074_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_dec(v_a_2070_);
lean_dec(v_a_2062_);
return v___x_2071_;
}
}
else
{
lean_dec(v_a_2062_);
return v___x_2069_;
}
}
else
{
lean_dec_ref(v___y_2060_);
lean_dec(v_a_2054_);
lean_dec(v_a_2045_);
lean_dec_ref(v_runInBase_2039_);
return v___x_2061_;
}
}
}
else
{
lean_dec(v_a_2054_);
lean_dec(v_a_2045_);
lean_dec_ref(v_runInBase_2039_);
return v___x_2057_;
}
}
else
{
lean_dec(v_a_2045_);
lean_dec_ref(v_runInBase_2039_);
return v___x_2053_;
}
}
}
else
{
lean_del_object(v___x_2041_);
lean_dec_ref(v_runInBase_2039_);
return v___x_2043_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_mkBreak_0interp(lean_interpreter_value* stack)
{
lean_object* v_base_2028_ = stack[0].m_obj;
uint8_t v_hasContinue_2029_ = stack[1].m_num;
lean_object* v_a_2030_ = stack[2].m_obj;
lean_object* v_a_2031_ = stack[3].m_obj;
lean_object* v_a_2032_ = stack[4].m_obj;
lean_object* v_a_2033_ = stack[5].m_obj;
lean_object* v_a_2034_ = stack[6].m_obj;
lean_object* v_a_2035_ = stack[7].m_obj;
lean_object* v_a_2036_ = stack[8].m_obj;
lean_object* v_res_2101_;
v_res_2101_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2028_, v_hasContinue_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
stack->m_obj
 = v_res_2101_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object* v_base_2102_, lean_object* v_hasContinue_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
uint8_t v_hasContinue_boxed_2112_; lean_object* v_res_2113_; 
v_hasContinue_boxed_2112_ = lean_unbox(v_hasContinue_2103_);
v_res_2113_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2102_, v_hasContinue_boxed_2112_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_a_2104_);
return v_res_2113_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object* v_base_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_m_2128_; lean_object* v_runInBase_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2180_; 
v_m_2128_ = lean_ctor_get(v_base_2119_, 1);
v_runInBase_2129_ = lean_ctor_get(v_base_2119_, 3);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_base_2119_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2181_ = lean_ctor_get(v_base_2119_, 4);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_base_2119_, 2);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_base_2119_, 0);
lean_dec(v_unused_2183_);
v___x_2131_ = v_base_2119_;
v_isShared_2132_ = v_isSharedCheck_2180_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_runInBase_2129_);
lean_inc(v_m_2128_);
lean_dec(v_base_2119_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2180_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; 
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_a_2122_);
lean_inc_ref(v_a_2121_);
lean_inc_ref(v_a_2120_);
v___x_2133_ = lean_apply_8(v_m_2128_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, lean_box(0));
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_monadInfo_2134_; lean_object* v_a_2135_; lean_object* v_doBlockResultType_2136_; lean_object* v_u_2137_; lean_object* v_v_2138_; lean_object* v_cachedPUnit_2139_; lean_object* v_cachedPUnitUnit_2140_; lean_object* v___x_2142_; 
v_monadInfo_2134_ = lean_ctor_get(v_a_2120_, 0);
v_a_2135_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_n(v_a_2135_, 2);
lean_dec_ref_known(v___x_2133_, 1);
v_doBlockResultType_2136_ = lean_ctor_get(v_a_2120_, 3);
v_u_2137_ = lean_ctor_get(v_monadInfo_2134_, 1);
v_v_2138_ = lean_ctor_get(v_monadInfo_2134_, 2);
v_cachedPUnit_2139_ = lean_ctor_get(v_monadInfo_2134_, 3);
v_cachedPUnitUnit_2140_ = lean_ctor_get(v_monadInfo_2134_, 4);
lean_inc_ref(v_cachedPUnitUnit_2140_);
lean_inc_ref(v_cachedPUnit_2139_);
lean_inc(v_v_2138_);
lean_inc(v_u_2137_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 4, v_cachedPUnitUnit_2140_);
lean_ctor_set(v___x_2131_, 3, v_cachedPUnit_2139_);
lean_ctor_set(v___x_2131_, 2, v_v_2138_);
lean_ctor_set(v___x_2131_, 1, v_u_2137_);
lean_ctor_set(v___x_2131_, 0, v_a_2135_);
v___x_2142_ = v___x_2131_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2135_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_u_2137_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2138_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_cachedPUnit_2139_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_cachedPUnitUnit_2140_);
v___x_2142_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2142_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2146_ = 0;
v___x_2147_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2145_, v___x_2146_, v_a_2120_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
lean_inc_ref(v_doBlockResultType_2136_);
v___x_2149_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2136_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1));
v___x_2152_ = lean_box(0);
lean_inc(v_v_2138_);
v___x_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_v_2138_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
lean_inc(v_u_2137_);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_u_2137_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_mkConst(v___x_2151_, v___x_2154_);
v___x_2156_ = l_Lean_mkApp3(v___x_2155_, v_a_2148_, v_a_2135_, v_a_2144_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_a_2122_);
lean_inc_ref(v_a_2121_);
lean_inc_ref(v_a_2120_);
v___x_2157_ = lean_apply_9(v_runInBase_2129_, v___x_2156_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, lean_box(0));
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc_n(v_a_2158_, 2);
lean_dec_ref_known(v___x_2157_, 1);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
v___x_2159_ = lean_infer_type(v_a_2158_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2));
v___x_2162_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2161_, v_a_2150_, v_a_2160_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v___x_2162_, 0);
lean_dec(v_unused_2170_);
v___x_2164_ = v___x_2162_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2162_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v_a_2158_);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2158_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_a_2158_);
v_a_2171_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2162_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2162_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_dec(v_a_2158_);
lean_dec(v_a_2150_);
return v___x_2159_;
}
}
else
{
lean_dec(v_a_2150_);
return v___x_2157_;
}
}
else
{
lean_dec(v_a_2148_);
lean_dec(v_a_2144_);
lean_dec(v_a_2135_);
lean_dec_ref(v_runInBase_2129_);
return v___x_2149_;
}
}
else
{
lean_dec(v_a_2144_);
lean_dec(v_a_2135_);
lean_dec_ref(v_runInBase_2129_);
return v___x_2147_;
}
}
else
{
lean_dec(v_a_2135_);
lean_dec_ref(v_runInBase_2129_);
return v___x_2143_;
}
}
}
else
{
lean_del_object(v___x_2131_);
lean_dec_ref(v_runInBase_2129_);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_mkContinue_0interp(lean_interpreter_value* stack)
{
lean_object* v_base_2119_ = stack[0].m_obj;
lean_object* v_a_2120_ = stack[1].m_obj;
lean_object* v_a_2121_ = stack[2].m_obj;
lean_object* v_a_2122_ = stack[3].m_obj;
lean_object* v_a_2123_ = stack[4].m_obj;
lean_object* v_a_2124_ = stack[5].m_obj;
lean_object* v_a_2125_ = stack[6].m_obj;
lean_object* v_a_2126_ = stack[7].m_obj;
lean_object* v_res_2184_;
v_res_2184_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
stack->m_obj
 = v_res_2184_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object* v_base_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec_ref(v_a_2186_);
return v_res_2194_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object* v_base_2203_, lean_object* v_r_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_m_2213_; lean_object* v_runInBase_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2260_; 
v_m_2213_ = lean_ctor_get(v_base_2203_, 1);
v_runInBase_2214_ = lean_ctor_get(v_base_2203_, 3);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_base_2203_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2261_ = lean_ctor_get(v_base_2203_, 4);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_base_2203_, 2);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_base_2203_, 0);
lean_dec(v_unused_2263_);
v___x_2216_ = v_base_2203_;
v_isShared_2217_ = v_isSharedCheck_2260_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_runInBase_2214_);
lean_inc(v_m_2213_);
lean_dec(v_base_2203_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2260_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; 
lean_inc(v_a_2211_);
lean_inc_ref(v_a_2210_);
lean_inc(v_a_2209_);
lean_inc_ref(v_a_2208_);
lean_inc(v_a_2207_);
lean_inc_ref(v_a_2206_);
lean_inc_ref(v_a_2205_);
v___x_2218_ = lean_apply_8(v_m_2213_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, lean_box(0));
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_monadInfo_2219_; lean_object* v_a_2220_; lean_object* v_doBlockResultType_2221_; lean_object* v_u_2222_; lean_object* v_v_2223_; lean_object* v_cachedPUnit_2224_; lean_object* v_cachedPUnitUnit_2225_; lean_object* v___x_2227_; 
v_monadInfo_2219_ = lean_ctor_get(v_a_2205_, 0);
v_a_2220_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_n(v_a_2220_, 2);
lean_dec_ref_known(v___x_2218_, 1);
v_doBlockResultType_2221_ = lean_ctor_get(v_a_2205_, 3);
v_u_2222_ = lean_ctor_get(v_monadInfo_2219_, 1);
v_v_2223_ = lean_ctor_get(v_monadInfo_2219_, 2);
v_cachedPUnit_2224_ = lean_ctor_get(v_monadInfo_2219_, 3);
v_cachedPUnitUnit_2225_ = lean_ctor_get(v_monadInfo_2219_, 4);
lean_inc_ref(v_cachedPUnitUnit_2225_);
lean_inc_ref(v_cachedPUnit_2224_);
lean_inc(v_v_2223_);
lean_inc(v_u_2222_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 4, v_cachedPUnitUnit_2225_);
lean_ctor_set(v___x_2216_, 3, v_cachedPUnit_2224_);
lean_ctor_set(v___x_2216_, 2, v_v_2223_);
lean_ctor_set(v___x_2216_, 1, v_u_2222_);
lean_ctor_set(v___x_2216_, 0, v_a_2220_);
v___x_2227_ = v___x_2216_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2220_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_u_2222_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_v_2223_);
lean_ctor_set(v_reuseFailAlloc_2259_, 3, v_cachedPUnit_2224_);
lean_ctor_set(v_reuseFailAlloc_2259_, 4, v_cachedPUnitUnit_2225_);
v___x_2227_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2227_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
lean_inc(v_a_2211_);
lean_inc_ref(v_a_2210_);
lean_inc(v_a_2209_);
lean_inc_ref(v_a_2208_);
lean_inc_ref(v_r_2204_);
v___x_2230_ = lean_infer_type(v_r_2204_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1));
v___x_2233_ = 0;
v___x_2234_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2232_, v___x_2233_, v_a_2205_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
lean_inc_ref(v_doBlockResultType_2221_);
v___x_2236_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2221_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
v___x_2239_ = lean_box(0);
lean_inc(v_v_2223_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_v_2223_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
lean_inc(v_u_2222_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_u_2222_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
lean_inc_ref(v___x_2241_);
v___x_2242_ = l_Lean_mkConst(v___x_2238_, v___x_2241_);
lean_inc(v_a_2235_);
lean_inc(v_a_2231_);
v___x_2243_ = l_Lean_mkAppB(v___x_2242_, v_a_2231_, v_a_2235_);
lean_inc(v_a_2220_);
v___x_2244_ = l_Lean_Expr_app___override(v_a_2220_, v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2));
v___x_2246_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2245_, v_a_2237_, v___x_2244_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec_ref_known(v___x_2246_, 1);
v___x_2247_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4));
v___x_2248_ = l_Lean_mkConst(v___x_2247_, v___x_2241_);
v___x_2249_ = l_Lean_mkApp5(v___x_2248_, v_a_2231_, v_a_2220_, v_a_2235_, v_a_2229_, v_r_2204_);
lean_inc(v_a_2211_);
lean_inc_ref(v_a_2210_);
lean_inc(v_a_2209_);
lean_inc_ref(v_a_2208_);
lean_inc(v_a_2207_);
lean_inc_ref(v_a_2206_);
lean_inc_ref(v_a_2205_);
v___x_2250_ = lean_apply_9(v_runInBase_2214_, v___x_2249_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, lean_box(0));
return v___x_2250_;
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref_known(v___x_2241_, 2);
lean_dec(v_a_2235_);
lean_dec(v_a_2231_);
lean_dec(v_a_2229_);
lean_dec(v_a_2220_);
lean_dec_ref(v_runInBase_2214_);
lean_dec_ref(v_r_2204_);
v_a_2251_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2246_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2246_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_dec(v_a_2235_);
lean_dec(v_a_2231_);
lean_dec(v_a_2229_);
lean_dec(v_a_2220_);
lean_dec_ref(v_runInBase_2214_);
lean_dec_ref(v_r_2204_);
return v___x_2236_;
}
}
else
{
lean_dec(v_a_2231_);
lean_dec(v_a_2229_);
lean_dec(v_a_2220_);
lean_dec_ref(v_runInBase_2214_);
lean_dec_ref(v_r_2204_);
return v___x_2234_;
}
}
else
{
lean_dec(v_a_2229_);
lean_dec(v_a_2220_);
lean_dec_ref(v_runInBase_2214_);
lean_dec_ref(v_r_2204_);
return v___x_2230_;
}
}
else
{
lean_dec(v_a_2220_);
lean_dec_ref(v_runInBase_2214_);
lean_dec_ref(v_r_2204_);
return v___x_2228_;
}
}
}
else
{
lean_del_object(v___x_2216_);
lean_dec_ref(v_runInBase_2214_);
lean_dec_ref(v_r_2204_);
return v___x_2218_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_mkReturn_0interp(lean_interpreter_value* stack)
{
lean_object* v_base_2203_ = stack[0].m_obj;
lean_object* v_r_2204_ = stack[1].m_obj;
lean_object* v_a_2205_ = stack[2].m_obj;
lean_object* v_a_2206_ = stack[3].m_obj;
lean_object* v_a_2207_ = stack[4].m_obj;
lean_object* v_a_2208_ = stack[5].m_obj;
lean_object* v_a_2209_ = stack[6].m_obj;
lean_object* v_a_2210_ = stack[7].m_obj;
lean_object* v_a_2211_ = stack[8].m_obj;
lean_object* v_res_2264_;
v_res_2264_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2203_, v_r_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
stack->m_obj
 = v_res_2264_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object* v_base_2265_, lean_object* v_r_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2265_, v_r_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2275_;
}
}
lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object* v_base_2290_, lean_object* v_resultName_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_m_2300_; lean_object* v_runInBase_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2334_; 
v_m_2300_ = lean_ctor_get(v_base_2290_, 1);
v_runInBase_2301_ = lean_ctor_get(v_base_2290_, 3);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_base_2290_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; lean_object* v_unused_2336_; lean_object* v_unused_2337_; 
v_unused_2335_ = lean_ctor_get(v_base_2290_, 4);
lean_dec(v_unused_2335_);
v_unused_2336_ = lean_ctor_get(v_base_2290_, 2);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_base_2290_, 0);
lean_dec(v_unused_2337_);
v___x_2303_ = v_base_2290_;
v_isShared_2304_ = v_isSharedCheck_2334_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_runInBase_2301_);
lean_inc(v_m_2300_);
lean_dec(v_base_2290_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2334_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; 
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc_ref(v_a_2292_);
v___x_2305_ = lean_apply_8(v_m_2300_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, lean_box(0));
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_monadInfo_2306_; lean_object* v_a_2307_; lean_object* v_u_2308_; lean_object* v_v_2309_; lean_object* v_cachedPUnit_2310_; lean_object* v_cachedPUnitUnit_2311_; lean_object* v___x_2313_; 
v_monadInfo_2306_ = lean_ctor_get(v_a_2292_, 0);
v_a_2307_ = lean_ctor_get(v___x_2305_, 0);
lean_inc_n(v_a_2307_, 2);
lean_dec_ref_known(v___x_2305_, 1);
v_u_2308_ = lean_ctor_get(v_monadInfo_2306_, 1);
v_v_2309_ = lean_ctor_get(v_monadInfo_2306_, 2);
v_cachedPUnit_2310_ = lean_ctor_get(v_monadInfo_2306_, 3);
v_cachedPUnitUnit_2311_ = lean_ctor_get(v_monadInfo_2306_, 4);
lean_inc_ref(v_cachedPUnitUnit_2311_);
lean_inc_ref(v_cachedPUnit_2310_);
lean_inc(v_v_2309_);
lean_inc(v_u_2308_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 4, v_cachedPUnitUnit_2311_);
lean_ctor_set(v___x_2303_, 3, v_cachedPUnit_2310_);
lean_ctor_set(v___x_2303_, 2, v_v_2309_);
lean_ctor_set(v___x_2303_, 1, v_u_2308_);
lean_ctor_set(v___x_2303_, 0, v_a_2307_);
v___x_2313_ = v___x_2303_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2307_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_u_2308_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2309_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_cachedPUnit_2310_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_cachedPUnitUnit_2311_);
v___x_2313_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2313_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__2));
v___x_2317_ = lean_box(0);
lean_inc(v_v_2309_);
v___x_2318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_v_2309_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
lean_inc(v_u_2308_);
v___x_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_u_2308_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_inc_ref_n(v___x_2319_, 2);
v___x_2320_ = l_Lean_mkConst(v___x_2316_, v___x_2319_);
v___x_2321_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__4));
v___x_2322_ = l_Lean_mkConst(v___x_2321_, v___x_2319_);
lean_inc_n(v_a_2307_, 2);
v___x_2323_ = l_Lean_mkAppB(v___x_2322_, v_a_2307_, v_a_2315_);
v___x_2324_ = l_Lean_mkAppB(v___x_2320_, v_a_2307_, v___x_2323_);
v___x_2325_ = l_Lean_Meta_getFVarFromUserName(v_resultName_2291_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_n(v_a_2326_, 2);
lean_dec_ref_known(v___x_2325_, 1);
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
v___x_2327_ = lean_infer_type(v_a_2326_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__7));
v___x_2330_ = l_Lean_mkConst(v___x_2329_, v___x_2319_);
v___x_2331_ = l_Lean_mkApp4(v___x_2330_, v_a_2307_, v___x_2324_, v_a_2328_, v_a_2326_);
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc_ref(v_a_2292_);
v___x_2332_ = lean_apply_9(v_runInBase_2301_, v___x_2331_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, lean_box(0));
return v___x_2332_;
}
else
{
lean_dec(v_a_2326_);
lean_dec_ref(v___x_2324_);
lean_dec_ref_known(v___x_2319_, 2);
lean_dec(v_a_2307_);
lean_dec_ref(v_runInBase_2301_);
return v___x_2327_;
}
}
else
{
lean_dec_ref(v___x_2324_);
lean_dec_ref_known(v___x_2319_, 2);
lean_dec(v_a_2307_);
lean_dec_ref(v_runInBase_2301_);
return v___x_2325_;
}
}
else
{
lean_dec(v_a_2307_);
lean_dec_ref(v_runInBase_2301_);
lean_dec(v_resultName_2291_);
return v___x_2314_;
}
}
}
else
{
lean_del_object(v___x_2303_);
lean_dec_ref(v_runInBase_2301_);
lean_dec(v_resultName_2291_);
return v___x_2305_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_ControlStack_mkPure_0interp(lean_interpreter_value* stack)
{
lean_object* v_base_2290_ = stack[0].m_obj;
lean_object* v_resultName_2291_ = stack[1].m_obj;
lean_object* v_a_2292_ = stack[2].m_obj;
lean_object* v_a_2293_ = stack[3].m_obj;
lean_object* v_a_2294_ = stack[4].m_obj;
lean_object* v_a_2295_ = stack[5].m_obj;
lean_object* v_a_2296_ = stack[6].m_obj;
lean_object* v_a_2297_ = stack[7].m_obj;
lean_object* v_a_2298_ = stack[8].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2290_, v_resultName_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object* v_base_2339_, lean_object* v_resultName_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2339_, v_resultName_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec_ref(v_a_2341_);
return v_res_2349_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(lean_object* v_info_2350_, lean_object* v_as_2351_, size_t v_i_2352_, size_t v_stop_2353_, lean_object* v_b_2354_){
_start:
{
lean_object* v___y_2356_; uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_eq(v_i_2352_, v_stop_2353_);
if (v___x_2360_ == 0)
{
lean_object* v_reassigns_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_reassigns_2361_ = lean_ctor_get(v_info_2350_, 1);
v___x_2362_ = lean_array_uget_borrowed(v_as_2351_, v_i_2352_);
v___x_2363_ = l_Lean_Elab_Do_MutVar_getId(v___x_2362_);
v___x_2364_ = l_Lean_NameSet_contains(v_reassigns_2361_, v___x_2363_);
lean_dec(v___x_2363_);
if (v___x_2364_ == 0)
{
v___y_2356_ = v_b_2354_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2365_; 
lean_inc(v___x_2362_);
v___x_2365_ = lean_array_push(v_b_2354_, v___x_2362_);
v___y_2356_ = v___x_2365_;
goto v___jp_2355_;
}
}
else
{
return v_b_2354_;
}
v___jp_2355_:
{
size_t v___x_2357_; size_t v___x_2358_; 
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_add(v_i_2352_, v___x_2357_);
v_i_2352_ = v___x_2358_;
v_b_2354_ = v___y_2356_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2350_ = stack[0].m_obj;
lean_object* v_as_2351_ = stack[1].m_obj;
size_t v_i_2352_ = stack[2].m_num;
size_t v_stop_2353_ = stack[3].m_num;
lean_object* v_b_2354_ = stack[4].m_obj;
lean_object* v_res_2366_;
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2350_, v_as_2351_, v_i_2352_, v_stop_2353_, v_b_2354_);
stack->m_obj
 = v_res_2366_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0___boxed(lean_object* v_info_2367_, lean_object* v_as_2368_, lean_object* v_i_2369_, lean_object* v_stop_2370_, lean_object* v_b_2371_){
_start:
{
size_t v_i_boxed_2372_; size_t v_stop_boxed_2373_; lean_object* v_res_2374_; 
v_i_boxed_2372_ = lean_unbox_usize(v_i_2369_);
lean_dec(v_i_2369_);
v_stop_boxed_2373_ = lean_unbox_usize(v_stop_2370_);
lean_dec(v_stop_2370_);
v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2367_, v_as_2368_, v_i_boxed_2372_, v_stop_boxed_2373_, v_b_2371_);
lean_dec_ref(v_as_2368_);
lean_dec_ref(v_info_2367_);
return v_res_2374_;
}
}
lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object* v_info_2377_, lean_object* v_dec_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v_continueBase_x3f_2390_; lean_object* v_controlStack_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v_monadInfo_2419_; lean_object* v_mutVars_2420_; lean_object* v___y_2422_; lean_object* v___y_2423_; uint8_t v___y_2424_; lean_object* v_breakBase_x3f_2425_; lean_object* v_controlStack_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2437_; lean_object* v___y_2438_; uint8_t v___y_2439_; uint8_t v___y_2440_; lean_object* v_controlStack_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2452_; lean_object* v___y_2453_; uint8_t v___y_2454_; uint8_t v___y_2455_; lean_object* v_returnBase_x3f_2456_; lean_object* v_controlStack_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2470_; uint8_t v___y_2471_; uint8_t v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; uint8_t v___y_2489_; uint8_t v___y_2490_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2531_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_monadInfo_2419_ = lean_ctor_get(v_a_2379_, 0);
v_mutVars_2420_ = lean_ctor_get(v_a_2379_, 1);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_array_get_size(v_mutVars_2420_);
v___x_2572_ = ((lean_object*)(l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0));
v___x_2573_ = lean_nat_dec_lt(v___x_2570_, v___x_2571_);
if (v___x_2573_ == 0)
{
v___y_2531_ = v___x_2572_;
goto v___jp_2530_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_nat_dec_le(v___x_2571_, v___x_2571_);
if (v___x_2574_ == 0)
{
if (v___x_2573_ == 0)
{
v___y_2531_ = v___x_2572_;
goto v___jp_2530_;
}
else
{
size_t v___x_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = lean_usize_of_nat(v___x_2571_);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2377_, v_mutVars_2420_, v___x_2575_, v___x_2576_, v___x_2572_);
v___y_2531_ = v___x_2577_;
goto v___jp_2530_;
}
}
else
{
size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = lean_usize_of_nat(v___x_2571_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2377_, v_mutVars_2420_, v___x_2578_, v___x_2579_, v___x_2572_);
v___y_2531_ = v___x_2580_;
goto v___jp_2530_;
}
}
v___jp_2387_:
{
lean_object* v_stM_2399_; lean_object* v_resultType_2400_; lean_object* v___x_2401_; 
v_stM_2399_ = lean_ctor_get(v_controlStack_2391_, 2);
v_resultType_2400_ = lean_ctor_get(v_dec_2378_, 1);
lean_inc_ref(v_stM_2399_);
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
lean_inc(v___y_2394_);
lean_inc_ref(v___y_2393_);
lean_inc_ref(v___y_2392_);
lean_inc_ref(v_resultType_2400_);
v___x_2401_ = lean_apply_9(v_stM_2399_, v_resultType_2400_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, lean_box(0));
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2410_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2410_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2410_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2406_, 0, v_dec_2378_);
lean_ctor_set(v___x_2406_, 1, v___y_2388_);
lean_ctor_set(v___x_2406_, 2, v___y_2389_);
lean_ctor_set(v___x_2406_, 3, v_continueBase_x3f_2390_);
lean_ctor_set(v___x_2406_, 4, v_controlStack_2391_);
lean_ctor_set(v___x_2406_, 5, v_a_2402_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2406_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v_controlStack_2391_);
lean_dec(v_continueBase_x3f_2390_);
lean_dec(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v_dec_2378_);
v_a_2411_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2401_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2401_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
v___jp_2421_:
{
if (v___y_2424_ == 0)
{
v___y_2388_ = v___y_2422_;
v___y_2389_ = v_breakBase_x3f_2425_;
v_continueBase_x3f_2390_ = v___y_2423_;
v_controlStack_2391_ = v_controlStack_2426_;
v___y_2392_ = v___y_2427_;
v___y_2393_ = v___y_2428_;
v___y_2394_ = v___y_2429_;
v___y_2395_ = v___y_2430_;
v___y_2396_ = v___y_2431_;
v___y_2397_ = v___y_2432_;
v___y_2398_ = v___y_2433_;
goto v___jp_2387_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec(v___y_2423_);
lean_inc_ref(v_controlStack_2426_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_controlStack_2426_);
lean_inc_ref(v_monadInfo_2419_);
v___x_2435_ = l_Lean_Elab_Do_ControlStack_continueT(v_monadInfo_2419_, v_controlStack_2426_);
v___y_2388_ = v___y_2422_;
v___y_2389_ = v_breakBase_x3f_2425_;
v_continueBase_x3f_2390_ = v___x_2434_;
v_controlStack_2391_ = v___x_2435_;
v___y_2392_ = v___y_2427_;
v___y_2393_ = v___y_2428_;
v___y_2394_ = v___y_2429_;
v___y_2395_ = v___y_2430_;
v___y_2396_ = v___y_2431_;
v___y_2397_ = v___y_2432_;
v___y_2398_ = v___y_2433_;
goto v___jp_2387_;
}
}
v___jp_2436_:
{
if (v___y_2440_ == 0)
{
lean_inc(v___y_2438_);
v___y_2422_ = v___y_2437_;
v___y_2423_ = v___y_2438_;
v___y_2424_ = v___y_2439_;
v_breakBase_x3f_2425_ = v___y_2438_;
v_controlStack_2426_ = v_controlStack_2441_;
v___y_2427_ = v___y_2442_;
v___y_2428_ = v___y_2443_;
v___y_2429_ = v___y_2444_;
v___y_2430_ = v___y_2445_;
v___y_2431_ = v___y_2446_;
v___y_2432_ = v___y_2447_;
v___y_2433_ = v___y_2448_;
goto v___jp_2421_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_inc_ref(v_controlStack_2441_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_controlStack_2441_);
lean_inc_ref(v_monadInfo_2419_);
v___x_2450_ = l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_2419_, v_controlStack_2441_);
v___y_2422_ = v___y_2437_;
v___y_2423_ = v___y_2438_;
v___y_2424_ = v___y_2439_;
v_breakBase_x3f_2425_ = v___x_2449_;
v_controlStack_2426_ = v___x_2450_;
v___y_2427_ = v___y_2442_;
v___y_2428_ = v___y_2443_;
v___y_2429_ = v___y_2444_;
v___y_2430_ = v___y_2445_;
v___y_2431_ = v___y_2446_;
v___y_2432_ = v___y_2447_;
v___y_2433_ = v___y_2448_;
goto v___jp_2421_;
}
}
v___jp_2451_:
{
if (lean_obj_tag(v___y_2453_) == 1)
{
lean_object* v_val_2465_; lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2468_; 
v_val_2465_ = lean_ctor_get(v___y_2453_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v___y_2453_, 1);
v_fst_2466_ = lean_ctor_get(v_val_2465_, 0);
lean_inc(v_fst_2466_);
v_snd_2467_ = lean_ctor_get(v_val_2465_, 1);
lean_inc(v_snd_2467_);
lean_dec(v_val_2465_);
lean_inc_ref(v_monadInfo_2419_);
v___x_2468_ = l_Lean_Elab_Do_ControlStack_stateT(v_monadInfo_2419_, v_fst_2466_, v_snd_2467_, v_controlStack_2457_);
v___y_2437_ = v_returnBase_x3f_2456_;
v___y_2438_ = v___y_2452_;
v___y_2439_ = v___y_2454_;
v___y_2440_ = v___y_2455_;
v_controlStack_2441_ = v___x_2468_;
v___y_2442_ = v___y_2458_;
v___y_2443_ = v___y_2459_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2461_;
v___y_2446_ = v___y_2462_;
v___y_2447_ = v___y_2463_;
v___y_2448_ = v___y_2464_;
goto v___jp_2436_;
}
else
{
lean_dec(v___y_2453_);
v___y_2437_ = v_returnBase_x3f_2456_;
v___y_2438_ = v___y_2452_;
v___y_2439_ = v___y_2454_;
v___y_2440_ = v___y_2455_;
v_controlStack_2441_ = v_controlStack_2457_;
v___y_2442_ = v___y_2458_;
v___y_2443_ = v___y_2459_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2461_;
v___y_2446_ = v___y_2462_;
v___y_2447_ = v___y_2463_;
v___y_2448_ = v___y_2464_;
goto v___jp_2436_;
}
}
v___jp_2469_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_box(0);
lean_inc_ref(v_monadInfo_2419_);
v___x_2475_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_2419_);
if (lean_obj_tag(v___y_2470_) == 1)
{
lean_object* v_val_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2484_; 
v_val_2476_ = lean_ctor_get(v___y_2470_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___y_2470_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2478_ = v___y_2470_;
v_isShared_2479_ = v_isSharedCheck_2484_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_val_2476_);
lean_dec(v___y_2470_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2484_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
lean_inc_ref(v___x_2475_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2475_);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2475_);
v___x_2481_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; 
lean_inc_ref(v_monadInfo_2419_);
v___x_2482_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(v_monadInfo_2419_, v_val_2476_, v___x_2475_);
v___y_2452_ = v___x_2474_;
v___y_2453_ = v___y_2473_;
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2472_;
v_returnBase_x3f_2456_ = v___x_2481_;
v_controlStack_2457_ = v___x_2482_;
v___y_2458_ = v_a_2379_;
v___y_2459_ = v_a_2380_;
v___y_2460_ = v_a_2381_;
v___y_2461_ = v_a_2382_;
v___y_2462_ = v_a_2383_;
v___y_2463_ = v_a_2384_;
v___y_2464_ = v_a_2385_;
goto v___jp_2451_;
}
}
}
else
{
lean_dec(v___y_2470_);
v___y_2452_ = v___x_2474_;
v___y_2453_ = v___y_2473_;
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2472_;
v_returnBase_x3f_2456_ = v___x_2474_;
v_controlStack_2457_ = v___x_2475_;
v___y_2458_ = v_a_2379_;
v___y_2459_ = v_a_2380_;
v___y_2460_ = v_a_2381_;
v___y_2461_ = v_a_2382_;
v___y_2462_ = v_a_2383_;
v___y_2463_ = v_a_2384_;
v___y_2464_ = v_a_2385_;
goto v___jp_2451_;
}
}
v___jp_2485_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2491_ = lean_array_get_size(v___y_2487_);
v___x_2492_ = lean_unsigned_to_nat(0u);
v___x_2493_ = lean_nat_dec_eq(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___y_2487_);
lean_ctor_set(v___x_2494_, 1, v___y_2488_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
v___y_2470_ = v___y_2486_;
v___y_2471_ = v___y_2490_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___x_2495_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2496_; 
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___y_2487_);
v___x_2496_ = lean_box(0);
v___y_2470_ = v___y_2486_;
v___y_2471_ = v___y_2490_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___x_2496_;
goto v___jp_2469_;
}
}
v___jp_2497_:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2379_);
if (lean_obj_tag(v___x_2502_) == 0)
{
uint8_t v_continues_2503_; 
v_continues_2503_ = lean_ctor_get_uint8(v_info_2377_, sizeof(void*)*2 + 1);
if (v_continues_2503_ == 0)
{
lean_dec_ref_known(v___x_2502_, 1);
v___y_2486_ = v___y_2498_;
v___y_2487_ = v___y_2499_;
v___y_2488_ = v___y_2500_;
v___y_2489_ = v___y_2501_;
v___y_2490_ = v_continues_2503_;
goto v___jp_2485_;
}
else
{
lean_object* v_a_2504_; 
v_a_2504_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2502_, 1);
if (lean_obj_tag(v_a_2504_) == 0)
{
uint8_t v___x_2505_; 
v___x_2505_ = 0;
v___y_2486_ = v___y_2498_;
v___y_2487_ = v___y_2499_;
v___y_2488_ = v___y_2500_;
v___y_2489_ = v___y_2501_;
v___y_2490_ = v___x_2505_;
goto v___jp_2485_;
}
else
{
lean_dec_ref_known(v_a_2504_, 1);
v___y_2486_ = v___y_2498_;
v___y_2487_ = v___y_2499_;
v___y_2488_ = v___y_2500_;
v___y_2489_ = v___y_2501_;
v___y_2490_ = v_continues_2503_;
goto v___jp_2485_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v_dec_2378_);
v_a_2506_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
v___jp_2514_:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2379_);
if (lean_obj_tag(v___x_2518_) == 0)
{
uint8_t v_breaks_2519_; 
v_breaks_2519_ = lean_ctor_get_uint8(v_info_2377_, sizeof(void*)*2);
if (v_breaks_2519_ == 0)
{
lean_dec_ref_known(v___x_2518_, 1);
v___y_2498_ = v___y_2517_;
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___y_2516_;
v___y_2501_ = v_breaks_2519_;
goto v___jp_2497_;
}
else
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2518_, 1);
if (lean_obj_tag(v_a_2520_) == 0)
{
uint8_t v___x_2521_; 
v___x_2521_ = 0;
v___y_2498_ = v___y_2517_;
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___y_2516_;
v___y_2501_ = v___x_2521_;
goto v___jp_2497_;
}
else
{
lean_dec_ref_known(v_a_2520_, 1);
v___y_2498_ = v___y_2517_;
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___y_2516_;
v___y_2501_ = v_breaks_2519_;
goto v___jp_2497_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v_dec_2378_);
v_a_2522_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2518_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2518_);
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
v___jp_2530_:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2379_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v_resultType_2534_; size_t v_sz_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v_resultType_2534_ = lean_ctor_get(v_a_2533_, 0);
lean_inc_ref(v_resultType_2534_);
lean_dec(v_a_2533_);
v_sz_2535_ = lean_array_size(v___y_2531_);
v___x_2536_ = ((size_t)0ULL);
lean_inc_ref(v___y_2531_);
v___x_2537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_2535_, v___x_2536_, v___y_2531_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v_u_2539_; lean_object* v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v_u_2539_ = lean_ctor_get(v_monadInfo_2419_, 1);
lean_inc(v_u_2539_);
v___x_2540_ = l_Lean_Meta_mkProdN(v_a_2538_, v_u_2539_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
if (lean_obj_tag(v___x_2540_) == 0)
{
uint8_t v_returnsEarly_2541_; 
v_returnsEarly_2541_ = lean_ctor_get_uint8(v_info_2377_, sizeof(void*)*2 + 2);
if (v_returnsEarly_2541_ == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
lean_dec_ref(v_resultType_2534_);
v_a_2542_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2540_, 1);
v___x_2543_ = lean_box(0);
v___y_2515_ = v___y_2531_;
v___y_2516_ = v_a_2542_;
v___y_2517_ = v___x_2543_;
goto v___jp_2514_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2540_, 1);
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_resultType_2534_);
v___y_2515_ = v___y_2531_;
v___y_2516_ = v_a_2544_;
v___y_2517_ = v___x_2545_;
goto v___jp_2514_;
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_resultType_2534_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_dec_2378_);
v_a_2546_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2540_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2540_);
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
lean_dec_ref(v_resultType_2534_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_dec_2378_);
v_a_2554_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2537_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2537_);
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
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_dec_2378_);
v_a_2562_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2532_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2532_);
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
}
}
LEAN_EXPORT void l_Lean_Elab_Do_EffectForwarder_ofCont_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2377_ = stack[0].m_obj;
lean_object* v_dec_2378_ = stack[1].m_obj;
lean_object* v_a_2379_ = stack[2].m_obj;
lean_object* v_a_2380_ = stack[3].m_obj;
lean_object* v_a_2381_ = stack[4].m_obj;
lean_object* v_a_2382_ = stack[5].m_obj;
lean_object* v_a_2383_ = stack[6].m_obj;
lean_object* v_a_2384_ = stack[7].m_obj;
lean_object* v_a_2385_ = stack[8].m_obj;
lean_object* v_res_2581_;
v_res_2581_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_info_2377_, v_dec_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
stack->m_obj
 = v_res_2581_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___boxed(lean_object* v_info_2582_, lean_object* v_dec_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_info_2582_, v_dec_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec_ref(v_info_2582_);
return v_res_2592_;
}
}
lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object* v_l_2593_, lean_object* v_elabElem_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2595_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2595_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2595_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2653_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
if (lean_obj_tag(v_a_2604_) == 1)
{
lean_object* v_breakBase_x3f_2664_; 
v_breakBase_x3f_2664_ = lean_ctor_get(v_l_2593_, 2);
lean_inc(v_breakBase_x3f_2664_);
if (lean_obj_tag(v_breakBase_x3f_2664_) == 1)
{
lean_object* v_continueBase_x3f_2665_; lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref_known(v_a_2604_, 1);
v_continueBase_x3f_2665_ = lean_ctor_get(v_l_2593_, 3);
v_val_2666_ = lean_ctor_get(v_breakBase_x3f_2664_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_breakBase_x3f_2664_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2668_ = v_breakBase_x3f_2664_;
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v_breakBase_x3f_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___y_2671_; 
if (lean_obj_tag(v_continueBase_x3f_2665_) == 0)
{
uint8_t v___x_2677_; 
v___x_2677_ = 0;
v___y_2671_ = v___x_2677_;
goto v___jp_2670_;
}
else
{
uint8_t v___x_2678_; 
v___x_2678_ = 1;
v___y_2671_ = v___x_2678_;
goto v___jp_2670_;
}
v___jp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2672_ = lean_box(v___y_2671_);
v___x_2673_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkBreak___boxed), 10, 2);
lean_closure_set(v___x_2673_, 0, v_val_2666_);
lean_closure_set(v___x_2673_, 1, v___x_2672_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
v___y_2653_ = v___x_2675_;
goto v___jp_2652_;
}
}
}
}
else
{
lean_dec(v_breakBase_x3f_2664_);
v___y_2653_ = v_a_2604_;
goto v___jp_2652_;
}
}
else
{
v___y_2653_ = v_a_2604_;
goto v___jp_2652_;
}
v___jp_2609_:
{
lean_object* v_origCont_2613_; lean_object* v_liftedStack_2614_; lean_object* v_liftedDoBlockResultType_2615_; lean_object* v_resultName_2616_; lean_object* v_resultType_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2635_; 
v_origCont_2613_ = lean_ctor_get(v_l_2593_, 0);
lean_inc_ref(v_origCont_2613_);
v_liftedStack_2614_ = lean_ctor_get(v_l_2593_, 4);
lean_inc_ref(v_liftedStack_2614_);
v_liftedDoBlockResultType_2615_ = lean_ctor_get(v_l_2593_, 5);
lean_inc_ref(v_liftedDoBlockResultType_2615_);
lean_dec_ref(v_l_2593_);
v_resultName_2616_ = lean_ctor_get(v_origCont_2613_, 0);
v_resultType_2617_ = lean_ctor_get(v_origCont_2613_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_origCont_2613_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v_origCont_2613_, 2);
lean_dec(v_unused_2636_);
v___x_2619_ = v_origCont_2613_;
v_isShared_2620_ = v_isSharedCheck_2635_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_resultType_2617_);
lean_inc(v_resultName_2616_);
lean_dec(v_origCont_2613_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2635_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_monadInfo_2621_; lean_object* v_mutVars_2622_; lean_object* v_mutVarDefs_2623_; uint8_t v_deadCode_2624_; lean_object* v_ops_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2631_; 
v_monadInfo_2621_ = lean_ctor_get(v_a_2595_, 0);
v_mutVars_2622_ = lean_ctor_get(v_a_2595_, 1);
v_mutVarDefs_2623_ = lean_ctor_get(v_a_2595_, 2);
v_deadCode_2624_ = lean_ctor_get_uint8(v_a_2595_, sizeof(void*)*6);
v_ops_2625_ = lean_ctor_get(v_a_2595_, 5);
lean_inc(v_resultName_2616_);
v___x_2626_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkPure___boxed), 10, 2);
lean_closure_set(v___x_2626_, 0, v_liftedStack_2614_);
lean_closure_set(v___x_2626_, 1, v_resultName_2616_);
v___x_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___y_2612_);
lean_ctor_set(v___x_2627_, 1, v___y_2610_);
lean_ctor_set(v___x_2627_, 2, v___y_2611_);
v___x_2628_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_2627_);
lean_dec_ref_known(v___x_2627_, 3);
v___x_2629_ = 1;
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 2, v___x_2626_);
v___x_2631_ = v___x_2619_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_resultName_2616_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_resultType_2617_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v___x_2626_);
v___x_2631_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_ctor_set_uint8(v___x_2631_, sizeof(void*)*3, v___x_2629_);
lean_inc(v_ops_2625_);
lean_inc_ref(v_mutVarDefs_2623_);
lean_inc_ref(v_mutVars_2622_);
lean_inc_ref(v_monadInfo_2621_);
v___x_2632_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2632_, 0, v_monadInfo_2621_);
lean_ctor_set(v___x_2632_, 1, v_mutVars_2622_);
lean_ctor_set(v___x_2632_, 2, v_mutVarDefs_2623_);
lean_ctor_set(v___x_2632_, 3, v_liftedDoBlockResultType_2615_);
lean_ctor_set(v___x_2632_, 4, v___x_2628_);
lean_ctor_set(v___x_2632_, 5, v_ops_2625_);
lean_ctor_set_uint8(v___x_2632_, sizeof(void*)*6, v_deadCode_2624_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
lean_inc(v_a_2599_);
lean_inc_ref(v_a_2598_);
lean_inc(v_a_2597_);
lean_inc_ref(v_a_2596_);
v___x_2633_ = lean_apply_9(v_elabElem_2594_, v___x_2631_, v___x_2632_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, lean_box(0));
return v___x_2633_;
}
}
}
v___jp_2637_:
{
lean_object* v_returnBase_x3f_2640_; 
v_returnBase_x3f_2640_ = lean_ctor_get(v_l_2593_, 1);
if (lean_obj_tag(v_returnBase_x3f_2640_) == 1)
{
lean_object* v_val_2641_; lean_object* v_resultType_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2650_; 
v_val_2641_ = lean_ctor_get(v_returnBase_x3f_2640_, 0);
v_resultType_2642_ = lean_ctor_get(v_a_2608_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_a_2608_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v_a_2608_, 1);
lean_dec(v_unused_2651_);
v___x_2644_ = v_a_2608_;
v_isShared_2645_ = v_isSharedCheck_2650_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_resultType_2642_);
lean_dec(v_a_2608_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2650_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_inc(v_val_2641_);
v___x_2646_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkReturn___boxed), 10, 1);
lean_closure_set(v___x_2646_, 0, v_val_2641_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2646_);
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_resultType_2642_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
v___y_2610_ = v___y_2638_;
v___y_2611_ = v___y_2639_;
v___y_2612_ = v___x_2648_;
goto v___jp_2609_;
}
}
}
else
{
v___y_2610_ = v___y_2638_;
v___y_2611_ = v___y_2639_;
v___y_2612_ = v_a_2608_;
goto v___jp_2609_;
}
}
v___jp_2652_:
{
if (lean_obj_tag(v_a_2606_) == 1)
{
lean_object* v_continueBase_x3f_2654_; 
v_continueBase_x3f_2654_ = lean_ctor_get(v_l_2593_, 3);
lean_inc(v_continueBase_x3f_2654_);
if (lean_obj_tag(v_continueBase_x3f_2654_) == 1)
{
lean_object* v_val_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref_known(v_a_2606_, 1);
v_val_2655_ = lean_ctor_get(v_continueBase_x3f_2654_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_continueBase_x3f_2654_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2657_ = v_continueBase_x3f_2654_;
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_val_2655_);
lean_dec(v_continueBase_x3f_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkContinue___boxed), 9, 1);
lean_closure_set(v___x_2659_, 0, v_val_2655_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v___y_2638_ = v___y_2653_;
v___y_2639_ = v___x_2661_;
goto v___jp_2637_;
}
}
}
else
{
lean_dec(v_continueBase_x3f_2654_);
v___y_2638_ = v___y_2653_;
v___y_2639_ = v_a_2606_;
goto v___jp_2637_;
}
}
else
{
v___y_2638_ = v___y_2653_;
v___y_2639_ = v_a_2606_;
goto v___jp_2637_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v_a_2606_);
lean_dec(v_a_2604_);
lean_dec_ref(v_elabElem_2594_);
lean_dec_ref(v_l_2593_);
v_a_2680_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2607_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2607_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2604_);
lean_dec_ref(v_elabElem_2594_);
lean_dec_ref(v_l_2593_);
v_a_2688_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2605_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2605_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v_elabElem_2594_);
lean_dec_ref(v_l_2593_);
v_a_2696_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2603_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2603_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_EffectForwarder_lift_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_2593_ = stack[0].m_obj;
lean_object* v_elabElem_2594_ = stack[1].m_obj;
lean_object* v_a_2595_ = stack[2].m_obj;
lean_object* v_a_2596_ = stack[3].m_obj;
lean_object* v_a_2597_ = stack[4].m_obj;
lean_object* v_a_2598_ = stack[5].m_obj;
lean_object* v_a_2599_ = stack[6].m_obj;
lean_object* v_a_2600_ = stack[7].m_obj;
lean_object* v_a_2601_ = stack[8].m_obj;
lean_object* v_res_2704_;
v_res_2704_ = l_Lean_Elab_Do_EffectForwarder_lift(v_l_2593_, v_elabElem_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
stack->m_obj
 = v_res_2704_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift___boxed(lean_object* v_l_2705_, lean_object* v_elabElem_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Elab_Do_EffectForwarder_lift(v_l_2705_, v_elabElem_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2715_;
}
}
lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object* v_l_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_liftedStack_2725_; lean_object* v_origCont_2726_; lean_object* v_restoreCont_2727_; lean_object* v___x_2728_; 
v_liftedStack_2725_ = lean_ctor_get(v_l_2716_, 4);
lean_inc_ref(v_liftedStack_2725_);
v_origCont_2726_ = lean_ctor_get(v_l_2716_, 0);
lean_inc_ref(v_origCont_2726_);
lean_dec_ref(v_l_2716_);
v_restoreCont_2727_ = lean_ctor_get(v_liftedStack_2725_, 4);
lean_inc_ref(v_restoreCont_2727_);
lean_dec_ref(v_liftedStack_2725_);
lean_inc(v_a_2723_);
lean_inc_ref(v_a_2722_);
lean_inc(v_a_2721_);
lean_inc_ref(v_a_2720_);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc_ref(v_a_2717_);
v___x_2728_ = lean_apply_9(v_restoreCont_2727_, v_origCont_2726_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, lean_box(0));
return v___x_2728_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_EffectForwarder_restoreCont_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_2716_ = stack[0].m_obj;
lean_object* v_a_2717_ = stack[1].m_obj;
lean_object* v_a_2718_ = stack[2].m_obj;
lean_object* v_a_2719_ = stack[3].m_obj;
lean_object* v_a_2720_ = stack[4].m_obj;
lean_object* v_a_2721_ = stack[5].m_obj;
lean_object* v_a_2722_ = stack[6].m_obj;
lean_object* v_a_2723_ = stack[7].m_obj;
lean_object* v_res_2729_;
v_res_2729_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_l_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
stack->m_obj
 = v_res_2729_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont___boxed(lean_object* v_l_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_l_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2739_;
}
}
lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_Control(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_Control(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_ProdN(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_Control(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_Control(builtin);
}
#ifdef __cplusplus
}
#endif
