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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__2));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__4));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__6));
v___x_61_ = l_Lean_stringToMessageData(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM(lean_object* v_m_62_, lean_object* v_stM_u03b1_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; 
v___x_72_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_73_ = 0;
v___x_74_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_72_, v___x_73_, v_a_64_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v_stM_76_; lean_object* v___x_77_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_n(v_a_75_, 2);
lean_dec_ref_known(v___x_74_, 1);
v_stM_76_ = lean_ctor_get(v_m_62_, 2);
lean_inc_ref(v_stM_76_);
lean_dec_ref(v_m_62_);
lean_inc(v_a_70_);
lean_inc_ref(v_a_69_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc_ref(v_a_64_);
v___x_77_ = lean_apply_9(v_stM_76_, v_a_75_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, lean_box(0));
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_79_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_n(v_a_78_, 2);
lean_dec_ref_known(v___x_77_, 1);
lean_inc_ref(v_stM_u03b1_63_);
v___x_79_ = l_Lean_Meta_isExprDefEq(v_stM_u03b1_63_, v_a_78_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_106_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_106_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_106_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_106_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint8_t v___x_84_; 
v___x_84_ = lean_unbox(v_a_80_);
lean_dec(v_a_80_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_del_object(v___x_82_);
lean_dec(v_a_75_);
v___x_85_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__3, &l_Lean_Elab_Do_ControlStack_unStM___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3);
v___x_86_ = l_Lean_MessageData_ofExpr(v_stM_u03b1_63_);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__5, &l_Lean_Elab_Do_ControlStack_unStM___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_MessageData_ofExpr(v_a_78_);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__7, &l_Lean_Elab_Do_ControlStack_unStM___closed__7_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_93_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v_a_78_);
lean_dec_ref(v_stM_u03b1_63_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v_a_75_);
v___x_104_ = v___x_82_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_75_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec(v_a_78_);
lean_dec(v_a_75_);
lean_dec_ref(v_stM_u03b1_63_);
v_a_107_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_79_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_79_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_dec(v_a_75_);
lean_dec_ref(v_stM_u03b1_63_);
return v___x_77_;
}
}
else
{
lean_dec_ref(v_stM_u03b1_63_);
lean_dec_ref(v_m_62_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM___boxed(lean_object* v_m_115_, lean_object* v_stM_u03b1_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Elab_Do_ControlStack_unStM(v_m_115_, v_stM_u03b1_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec_ref(v_a_117_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(lean_object* v_00_u03b1_126_, lean_object* v_msg_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_127_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___boxed(lean_object* v_00_u03b1_137_, lean_object* v_msg_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(v_00_u03b1_137_, v_msg_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0(lean_object* v_dec_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v_dec_148_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0___boxed(lean_object* v_dec_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_Do_ControlStack_base___lam__0(v_dec_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1(lean_object* v_00_u03b1_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v_00_u03b1_168_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1___boxed(lean_object* v_00_u03b1_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_Do_ControlStack_base___lam__1(v_00_u03b1_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_187_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1));
v___x_192_ = l_Lean_MessageData_ofFormat(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2(lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2, &l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once, _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3(lean_object* v_m_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_m_195_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3___boxed(lean_object* v_m_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_Do_ControlStack_base___lam__3(v_m_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base(lean_object* v_mi_218_){
_start:
{
lean_object* v_m_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_230_; 
v_m_219_ = lean_ctor_get(v_mi_218_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_mi_218_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_231_ = lean_ctor_get(v_mi_218_, 4);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_mi_218_, 3);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_mi_218_, 2);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_mi_218_, 1);
lean_dec(v_unused_234_);
v___x_221_ = v_mi_218_;
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_m_219_);
lean_dec(v_mi_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_230_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___x_228_; 
v___f_223_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__0));
v___f_224_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__1));
v___f_225_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__2));
v___f_226_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_base___lam__3___boxed), 9, 1);
lean_closure_set(v___f_226_, 0, v_m_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 4, v___f_223_);
lean_ctor_set(v___x_221_, 3, v___f_224_);
lean_ctor_set(v___x_221_, 2, v___f_224_);
lean_ctor_set(v___x_221_, 1, v___f_226_);
lean_ctor_set(v___x_221_, 0, v___f_225_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___f_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v___f_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(size_t v_sz_235_, size_t v_i_236_, lean_object* v_bs_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_lt(v_i_236_, v_sz_235_);
if (v___x_238_ == 0)
{
return v_bs_237_;
}
else
{
lean_object* v_v_239_; lean_object* v___x_240_; lean_object* v_bs_x27_241_; lean_object* v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; 
v_v_239_ = lean_array_uget(v_bs_237_, v_i_236_);
v___x_240_ = lean_unsigned_to_nat(0u);
v_bs_x27_241_ = lean_array_uset(v_bs_237_, v_i_236_, v___x_240_);
v___x_242_ = l_Lean_Elab_Do_MutVar_getId(v_v_239_);
lean_dec(v_v_239_);
v___x_243_ = ((size_t)1ULL);
v___x_244_ = lean_usize_add(v_i_236_, v___x_243_);
v___x_245_ = lean_array_uset(v_bs_x27_241_, v_i_236_, v___x_242_);
v_i_236_ = v___x_244_;
v_bs_237_ = v___x_245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0___boxed(lean_object* v_sz_247_, lean_object* v_i_248_, lean_object* v_bs_249_){
_start:
{
size_t v_sz_boxed_250_; size_t v_i_boxed_251_; lean_object* v_res_252_; 
v_sz_boxed_250_ = lean_unbox_usize(v_sz_247_);
lean_dec(v_sz_247_);
v_i_boxed_251_ = lean_unbox_usize(v_i_248_);
lean_dec(v_i_248_);
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_boxed_250_, v_i_boxed_251_, v_bs_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(lean_object* v_muts_253_){
_start:
{
size_t v_sz_254_; size_t v___x_255_; lean_object* v___x_256_; 
v_sz_254_ = lean_array_size(v_muts_253_);
v___x_255_ = ((size_t)0ULL);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_254_, v___x_255_, v_muts_253_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(size_t v_sz_257_, size_t v_i_258_, lean_object* v_bs_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_258_, v_sz_257_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_bs_259_);
return v___x_266_;
}
else
{
lean_object* v_v_267_; lean_object* v___x_268_; lean_object* v_bs_x27_269_; lean_object* v___x_270_; 
v_v_267_ = lean_array_uget(v_bs_259_, v_i_258_);
v___x_268_ = lean_unsigned_to_nat(0u);
v_bs_x27_269_ = lean_array_uset(v_bs_259_, v_i_258_, v___x_268_);
v___x_270_ = l_Lean_Elab_Do_MutVar_stateType(v_v_267_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v_v_267_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = ((size_t)1ULL);
v___x_273_ = lean_usize_add(v_i_258_, v___x_272_);
v___x_274_ = lean_array_uset(v_bs_x27_269_, v_i_258_, v_a_271_);
v_i_258_ = v___x_273_;
v_bs_259_ = v___x_274_;
goto _start;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_bs_x27_269_);
v_a_276_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_270_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_270_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg___boxed(lean_object* v_sz_284_, lean_object* v_i_285_, lean_object* v_bs_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
size_t v_sz_boxed_292_; size_t v_i_boxed_293_; lean_object* v_res_294_; 
v_sz_boxed_292_ = lean_unbox_usize(v_sz_284_);
lean_dec(v_sz_284_);
v_i_boxed_293_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_res_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_boxed_292_, v_i_boxed_293_, v_bs_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(lean_object* v_baseMonadInfo_295_, lean_object* v_muts_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
size_t v_sz_305_; size_t v___x_306_; lean_object* v___x_307_; 
v_sz_305_ = lean_array_size(v_muts_296_);
v___x_306_ = ((size_t)0ULL);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_305_, v___x_306_, v_muts_296_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_u_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_u_309_ = lean_ctor_get(v_baseMonadInfo_295_, 1);
lean_inc(v_u_309_);
lean_dec_ref(v_baseMonadInfo_295_);
v___x_310_ = l_Lean_Meta_mkProdN(v_a_308_, v_u_309_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
return v___x_310_;
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v_baseMonadInfo_295_);
v_a_311_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_307_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_307_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3___boxed(lean_object* v_baseMonadInfo_319_, lean_object* v_muts_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_319_, v_muts_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(size_t v_sz_330_, size_t v_i_331_, lean_object* v_bs_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_330_, v_i_331_, v_bs_332_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___boxed(lean_object* v_sz_342_, lean_object* v_i_343_, lean_object* v_bs_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_342_);
lean_dec(v_sz_342_);
v_i_boxed_354_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(v_sz_boxed_353_, v_i_boxed_354_, v_bs_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(lean_object* v_baseMonadInfo_359_, lean_object* v_muts_360_, lean_object* v_00_u03b1_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; 
lean_inc_ref(v_baseMonadInfo_359_);
v___x_370_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_359_, v_muts_360_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_385_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_385_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_385_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_385_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_u_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v_u_375_ = lean_ctor_get(v_baseMonadInfo_359_, 1);
lean_inc_n(v_u_375_, 2);
lean_dec_ref(v_baseMonadInfo_359_);
v___x_376_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1));
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v_u_375_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v_u_375_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = l_Lean_mkConst(v___x_376_, v___x_379_);
v___x_381_ = l_Lean_mkAppB(v___x_380_, v_00_u03b1_361_, v_a_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_381_);
v___x_383_ = v___x_373_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_dec_ref(v_00_u03b1_361_);
lean_dec_ref(v_baseMonadInfo_359_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___boxed(lean_object* v_baseMonadInfo_386_, lean_object* v_muts_387_, lean_object* v_00_u03b1_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_386_, v_muts_387_, v_00_u03b1_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec_ref(v_a_389_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0(lean_object* v_base_404_, lean_object* v_00_u03c3_405_, lean_object* v_x_406_){
_start:
{
lean_object* v_description_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_description_407_ = lean_ctor_get(v_base_404_, 0);
lean_inc_ref(v_description_407_);
lean_dec_ref(v_base_404_);
v___x_408_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1);
v___x_409_ = l_Lean_MessageData_ofExpr(v_00_u03c3_405_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_apply_1(v_description_407_, v___x_413_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_412_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1(lean_object* v_base_416_, lean_object* v_baseMonadInfo_417_, lean_object* v_muts_418_, lean_object* v_00_u03b1_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_stM_428_; lean_object* v___x_429_; 
v_stM_428_ = lean_ctor_get(v_base_416_, 2);
lean_inc_ref(v_stM_428_);
lean_dec_ref(v_base_416_);
v___x_429_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_417_, v_muts_418_, v_00_u03b1_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_431_ = lean_apply_9(v_stM_428_, v_a_430_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, lean_box(0));
return v___x_431_;
}
else
{
lean_dec_ref(v_stM_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(lean_object* v_base_432_, lean_object* v_baseMonadInfo_433_, lean_object* v_muts_434_, lean_object* v_00_u03b1_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(v_base_432_, v_baseMonadInfo_433_, v_muts_434_, v_00_u03b1_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2(lean_object* v_a_445_, lean_object* v_muts_446_, lean_object* v_resultName_447_, lean_object* v_k_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_getFVarFromUserName(v_a_445_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_muts_446_);
v___x_460_ = lean_array_to_list(v___x_459_);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v_resultName_447_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_Expr_fvarId_x21(v_a_458_);
lean_dec(v_a_458_);
v___x_463_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___x_461_, v___x_462_, v_k_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
return v___x_463_;
}
else
{
lean_dec_ref(v_k_448_);
lean_dec(v_resultName_447_);
lean_dec_ref(v_muts_446_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed(lean_object* v_a_464_, lean_object* v_muts_465_, lean_object* v_resultName_466_, lean_object* v_k_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Elab_Do_ControlStack_stateT___lam__2(v_a_464_, v_muts_465_, v_resultName_466_, v_k_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3(lean_object* v_muts_480_, lean_object* v_baseMonadInfo_481_, lean_object* v_base_482_, lean_object* v_dec_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1));
v___x_493_ = l_Lean_Core_mkFreshUserName(v___x_492_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_resultName_495_; lean_object* v_resultType_496_; lean_object* v_k_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_518_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_resultName_495_ = lean_ctor_get(v_dec_483_, 0);
v_resultType_496_ = lean_ctor_get(v_dec_483_, 1);
v_k_497_ = lean_ctor_get(v_dec_483_, 2);
v_isSharedCheck_518_ = !lean_is_exclusive(v_dec_483_);
if (v_isSharedCheck_518_ == 0)
{
v___x_499_ = v_dec_483_;
v_isShared_500_ = v_isSharedCheck_518_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_k_497_);
lean_inc(v_resultType_496_);
lean_inc(v_resultName_495_);
lean_dec(v_dec_483_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_518_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___f_501_; lean_object* v___x_502_; 
lean_inc_ref(v_muts_480_);
lean_inc(v_a_494_);
v___f_501_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed), 12, 4);
lean_closure_set(v___f_501_, 0, v_a_494_);
lean_closure_set(v___f_501_, 1, v_muts_480_);
lean_closure_set(v___f_501_, 2, v_resultName_495_);
lean_closure_set(v___f_501_, 3, v_k_497_);
v___x_502_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_481_, v_muts_480_, v_resultType_496_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_restoreCont_504_; uint8_t v___x_505_; lean_object* v___x_507_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v_restoreCont_504_ = lean_ctor_get(v_base_482_, 4);
lean_inc_ref(v_restoreCont_504_);
lean_dec_ref(v_base_482_);
v___x_505_ = 0;
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 2, v___f_501_);
lean_ctor_set(v___x_499_, 1, v_a_503_);
lean_ctor_set(v___x_499_, 0, v_a_494_);
v___x_507_ = v___x_499_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_a_503_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v___f_501_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3, v___x_505_);
lean_inc(v___y_490_);
lean_inc_ref(v___y_489_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc_ref(v___y_484_);
v___x_508_ = lean_apply_9(v_restoreCont_504_, v___x_507_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, lean_box(0));
return v___x_508_;
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v___f_501_);
lean_del_object(v___x_499_);
lean_dec(v_a_494_);
lean_dec_ref(v_base_482_);
v_a_510_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_502_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_502_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_dec_483_);
lean_dec_ref(v_base_482_);
lean_dec_ref(v_baseMonadInfo_481_);
lean_dec_ref(v_muts_480_);
v_a_519_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_493_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_493_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(lean_object* v_muts_527_, lean_object* v_baseMonadInfo_528_, lean_object* v_base_529_, lean_object* v_dec_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(v_muts_527_, v_baseMonadInfo_528_, v_base_529_, v_dec_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(size_t v_sz_540_, size_t v_i_541_, lean_object* v_bs_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_541_, v_sz_540_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_bs_542_);
return v___x_551_;
}
else
{
lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v_bs_x27_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_v_552_ = lean_array_uget(v_bs_542_, v_i_541_);
v___x_553_ = lean_unsigned_to_nat(0u);
v_bs_x27_554_ = lean_array_uset(v_bs_542_, v_i_541_, v___x_553_);
v___x_555_ = l_Lean_Elab_Do_MutVar_getId(v_v_552_);
v___x_556_ = l_Lean_Meta_getFVarFromUserName(v___x_555_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v_ident_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v_ident_558_ = lean_ctor_get(v_v_552_, 0);
v___x_559_ = lean_box(0);
v___x_560_ = lean_box(0);
v___x_561_ = 0;
lean_inc(v_ident_558_);
v___x_562_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_558_, v_a_557_, v___x_559_, v___x_559_, v___x_560_, v___x_561_, v___x_561_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
lean_dec_ref_known(v___x_562_, 1);
v___x_563_ = l_Lean_Elab_Do_MutVar_stateValue(v_v_552_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v_v_552_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_i_541_, v___x_565_);
v___x_567_ = lean_array_uset(v_bs_x27_554_, v_i_541_, v_a_564_);
v_i_541_ = v___x_566_;
v_bs_542_ = v___x_567_;
goto _start;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v_bs_x27_554_);
v_a_569_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_563_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_563_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v_bs_x27_554_);
lean_dec(v_v_552_);
v_a_577_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_562_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_562_);
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
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_bs_x27_554_);
lean_dec(v_v_552_);
v_a_585_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_556_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_556_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object* v_sz_593_, lean_object* v_i_594_, lean_object* v_bs_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
size_t v_sz_boxed_603_; size_t v_i_boxed_604_; lean_object* v_res_605_; 
v_sz_boxed_603_ = lean_unbox_usize(v_sz_593_);
lean_dec(v_sz_593_);
v_i_boxed_604_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_603_, v_i_boxed_604_, v_bs_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_605_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object* v_muts_615_, lean_object* v_baseMonadInfo_616_, lean_object* v_base_617_, lean_object* v_00_u03c3_618_, lean_object* v_e_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
size_t v_sz_628_; size_t v___x_629_; lean_object* v___x_630_; 
v_sz_628_ = lean_array_size(v_muts_615_);
v___x_629_ = ((size_t)0ULL);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_628_, v___x_629_, v_muts_615_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v_u_632_; lean_object* v___x_633_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v_u_632_ = lean_ctor_get(v_baseMonadInfo_616_, 1);
lean_inc(v_u_632_);
lean_dec_ref(v_baseMonadInfo_616_);
v___x_633_ = l_Lean_Meta_mkProdMkN(v_a_631_, v_u_632_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_682_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v_fst_635_ = lean_ctor_get(v_a_634_, 0);
v_snd_636_ = lean_ctor_get(v_a_634_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_a_634_);
if (v_isSharedCheck_682_ == 0)
{
v___x_638_ = v_a_634_;
v_isShared_639_ = v_isSharedCheck_682_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snd_636_);
lean_inc(v_fst_635_);
lean_dec(v_a_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_682_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___x_651_; 
lean_inc_ref(v_00_u03c3_618_);
lean_inc(v_snd_636_);
v___x_651_ = l_Lean_Meta_isExprDefEq(v_snd_636_, v_00_u03c3_618_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = lean_unbox(v_a_652_);
lean_dec(v_a_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_dec(v_fst_635_);
lean_dec_ref(v_e_619_);
lean_dec_ref(v_base_617_);
v___x_654_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1);
v___x_655_ = l_Lean_MessageData_ofExpr(v_00_u03c3_618_);
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 7);
lean_ctor_set(v___x_638_, 1, v___x_655_);
lean_ctor_set(v___x_638_, 0, v___x_654_);
v___x_657_ = v___x_638_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_673_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v___x_658_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_MessageData_ofExpr(v_snd_636_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_663_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_del_object(v___x_638_);
lean_dec(v_snd_636_);
lean_dec_ref(v_00_u03c3_618_);
v___y_641_ = v___y_620_;
v___y_642_ = v___y_621_;
v___y_643_ = v___y_622_;
v___y_644_ = v___y_623_;
v___y_645_ = v___y_624_;
v___y_646_ = v___y_625_;
v___y_647_ = v___y_626_;
goto v___jp_640_;
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_638_);
lean_dec(v_snd_636_);
lean_dec(v_fst_635_);
lean_dec_ref(v_e_619_);
lean_dec_ref(v_00_u03c3_618_);
lean_dec_ref(v_base_617_);
v_a_674_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_651_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_651_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
v___jp_640_:
{
lean_object* v_runInBase_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_runInBase_648_ = lean_ctor_get(v_base_617_, 3);
lean_inc_ref(v_runInBase_648_);
lean_dec_ref(v_base_617_);
v___x_649_ = l_Lean_Expr_app___override(v_e_619_, v_fst_635_);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_650_ = lean_apply_9(v_runInBase_648_, v___x_649_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, lean_box(0));
return v___x_650_;
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_e_619_);
lean_dec_ref(v_00_u03c3_618_);
lean_dec_ref(v_base_617_);
v_a_683_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_633_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_633_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_e_619_);
lean_dec_ref(v_00_u03c3_618_);
lean_dec_ref(v_base_617_);
lean_dec_ref(v_baseMonadInfo_616_);
v_a_691_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_630_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_630_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object* v_muts_699_, lean_object* v_baseMonadInfo_700_, lean_object* v_base_701_, lean_object* v_00_u03c3_702_, lean_object* v_e_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_muts_699_, v_baseMonadInfo_700_, v_base_701_, v_00_u03c3_702_, v_e_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object* v_baseMonadInfo_716_, lean_object* v_muts_717_, lean_object* v_base_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
lean_inc_ref(v_baseMonadInfo_716_);
v___x_727_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_716_, v_muts_717_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v_m_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v_m_729_ = lean_ctor_get(v_base_718_, 1);
lean_inc_ref(v_m_729_);
lean_dec_ref(v_base_718_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc_ref(v___y_719_);
v___x_730_ = lean_apply_8(v_m_729_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, lean_box(0));
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_746_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_746_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_746_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_746_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_u_735_; lean_object* v_v_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v_u_735_ = lean_ctor_get(v_baseMonadInfo_716_, 1);
lean_inc(v_u_735_);
v_v_736_ = lean_ctor_get(v_baseMonadInfo_716_, 2);
lean_inc(v_v_736_);
lean_dec_ref(v_baseMonadInfo_716_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1));
v___x_738_ = lean_box(0);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_v_736_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_u_735_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_mkConst(v___x_737_, v___x_740_);
v___x_742_ = l_Lean_mkAppB(v___x_741_, v_a_728_, v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_742_);
v___x_744_ = v___x_733_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_dec(v_a_728_);
lean_dec_ref(v_baseMonadInfo_716_);
return v___x_730_;
}
}
else
{
lean_dec_ref(v_base_718_);
lean_dec_ref(v_baseMonadInfo_716_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object* v_baseMonadInfo_747_, lean_object* v_muts_748_, lean_object* v_base_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_747_, v_muts_748_, v_base_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object* v_baseMonadInfo_759_, lean_object* v_muts_760_, lean_object* v_00_u03c3_761_, lean_object* v_base_762_){
_start:
{
lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
lean_inc_ref(v_00_u03c3_761_);
lean_inc_ref_n(v_base_762_, 4);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0), 3, 2);
lean_closure_set(v___f_763_, 0, v_base_762_);
lean_closure_set(v___f_763_, 1, v_00_u03c3_761_);
lean_inc_ref_n(v_muts_760_, 3);
lean_inc_ref_n(v_baseMonadInfo_759_, 3);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed), 12, 3);
lean_closure_set(v___f_764_, 0, v_base_762_);
lean_closure_set(v___f_764_, 1, v_baseMonadInfo_759_);
lean_closure_set(v___f_764_, 2, v_muts_760_);
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed), 12, 3);
lean_closure_set(v___f_765_, 0, v_muts_760_);
lean_closure_set(v___f_765_, 1, v_baseMonadInfo_759_);
lean_closure_set(v___f_765_, 2, v_base_762_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed), 13, 4);
lean_closure_set(v___f_766_, 0, v_muts_760_);
lean_closure_set(v___f_766_, 1, v_baseMonadInfo_759_);
lean_closure_set(v___f_766_, 2, v_base_762_);
lean_closure_set(v___f_766_, 3, v_00_u03c3_761_);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed), 11, 3);
lean_closure_set(v___f_767_, 0, v_baseMonadInfo_759_);
lean_closure_set(v___f_767_, 1, v_muts_760_);
lean_closure_set(v___f_767_, 2, v_base_762_);
v___x_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_768_, 0, v___f_763_);
lean_ctor_set(v___x_768_, 1, v___f_767_);
lean_ctor_set(v___x_768_, 2, v___f_764_);
lean_ctor_set(v___x_768_, 3, v___f_766_);
lean_ctor_set(v___x_768_, 4, v___f_765_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t v_sz_769_, size_t v_i_770_, lean_object* v_bs_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_769_, v_i_770_, v_bs_771_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object* v_sz_781_, lean_object* v_i_782_, lean_object* v_bs_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
size_t v_sz_boxed_792_; size_t v_i_boxed_793_; lean_object* v_res_794_; 
v_sz_boxed_792_ = lean_unbox_usize(v_sz_781_);
lean_dec(v_sz_781_);
v_i_boxed_793_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_792_, v_i_boxed_793_, v_bs_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object* v_baseMonadInfo_798_, lean_object* v_00_u03b1_799_){
_start:
{
lean_object* v_u_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_u_800_ = lean_ctor_get(v_baseMonadInfo_798_, 1);
v___x_801_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_802_ = lean_box(0);
lean_inc(v_u_800_);
v___x_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_803_, 0, v_u_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_mkConst(v___x_801_, v___x_803_);
v___x_805_ = l_Lean_Expr_app___override(v___x_804_, v_00_u03b1_799_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object* v_baseMonadInfo_806_, lean_object* v_00_u03b1_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_806_, v_00_u03b1_807_);
lean_dec_ref(v_baseMonadInfo_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object* v_runInBase_814_, lean_object* v_e_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_824_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2));
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_mk_empty_array_with_capacity(v___x_825_);
v___x_827_ = lean_array_push(v___x_826_, v_e_815_);
v___x_828_ = l_Lean_Meta_mkAppM(v___x_824_, v___x_827_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc_ref(v___y_816_);
v___x_830_ = lean_apply_9(v_runInBase_814_, v_a_829_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, lean_box(0));
return v___x_830_;
}
else
{
lean_dec_ref(v_runInBase_814_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object* v_runInBase_831_, lean_object* v_e_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_831_, v_e_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_841_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object* v_description_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1, &l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1);
v___x_848_ = lean_box(0);
v___x_849_ = lean_apply_1(v_description_845_, v___x_848_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_847_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object* v_dec_851_, lean_object* v_r_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_k_861_; lean_object* v___x_862_; 
v_k_861_ = lean_ctor_get(v_dec_851_, 2);
lean_inc_ref(v_k_861_);
lean_dec_ref(v_dec_851_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc_ref(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_862_ = lean_apply_8(v_k_861_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, lean_box(0));
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; uint8_t v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_mk_empty_array_with_capacity(v___x_864_);
v___x_866_ = lean_array_push(v___x_865_, v_r_852_);
v___x_867_ = 0;
v___x_868_ = 1;
v___x_869_ = 1;
v___x_870_ = l_Lean_Meta_mkLambdaFVars(v___x_866_, v_a_863_, v___x_867_, v___x_868_, v___x_867_, v___x_868_, v___x_869_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec_ref(v___x_866_);
return v___x_870_;
}
else
{
lean_dec_ref(v_r_852_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object* v_dec_871_, lean_object* v_r_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_dec_871_, v_r_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object* v_a_882_, lean_object* v_r_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc_ref(v___y_884_);
v___x_892_ = lean_apply_8(v_a_882_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, lean_box(0));
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; uint8_t v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_mk_empty_array_with_capacity(v___x_894_);
v___x_896_ = lean_array_push(v___x_895_, v_r_883_);
v___x_897_ = 0;
v___x_898_ = 1;
v___x_899_ = 1;
v___x_900_ = l_Lean_Meta_mkLambdaFVars(v___x_896_, v_a_893_, v___x_897_, v___x_898_, v___x_897_, v___x_898_, v___x_899_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec_ref(v___x_896_);
return v___x_900_;
}
else
{
lean_dec_ref(v_r_883_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object* v_a_901_, lean_object* v_r_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_901_, v_r_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object* v_k_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
lean_inc_ref(v___y_913_);
v___x_922_ = lean_apply_9(v_k_912_, v_b_916_, v___y_913_, v___y_914_, v___y_915_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, lean_box(0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_923_, v___y_924_, v___y_925_, v___y_926_, v_b_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object* v_name_934_, uint8_t v_bi_935_, lean_object* v_type_936_, lean_object* v_k_937_, uint8_t v_kind_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; 
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc_ref(v___y_939_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_947_, 0, v_k_937_);
lean_closure_set(v___f_947_, 1, v___y_939_);
lean_closure_set(v___f_947_, 2, v___y_940_);
lean_closure_set(v___f_947_, 3, v___y_941_);
v___x_948_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_934_, v_bi_935_, v_type_936_, v___f_947_, v_kind_938_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_948_) == 0)
{
return v___x_948_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object* v_name_957_, lean_object* v_bi_958_, lean_object* v_type_959_, lean_object* v_k_960_, lean_object* v_kind_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v_bi_boxed_970_; uint8_t v_kind_boxed_971_; lean_object* v_res_972_; 
v_bi_boxed_970_ = lean_unbox(v_bi_958_);
v_kind_boxed_971_ = lean_unbox(v_kind_961_);
v_res_972_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_957_, v_bi_boxed_970_, v_type_959_, v_k_960_, v_kind_boxed_971_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec_ref(v___y_962_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object* v_name_973_, lean_object* v_type_974_, lean_object* v_k_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = 0;
v___x_985_ = 0;
v___x_986_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_973_, v___x_984_, v_type_974_, v_k_975_, v___x_985_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object* v_name_987_, lean_object* v_type_988_, lean_object* v_k_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_987_, v_type_988_, v_k_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3));
v___x_1007_ = l_Lean_mkConst(v___x_1006_, v___x_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object* v_a_1008_, lean_object* v_getCont_1009_, lean_object* v_resultName_1010_, lean_object* v_resultType_1011_, lean_object* v___f_1012_, lean_object* v_baseMonadInfo_1013_, lean_object* v_casesOnWrapper_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_getFVarFromUserName(v_a_1008_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc_ref(v___y_1015_);
v___x_1025_ = lean_apply_8(v_getCont_1009_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___f_1027_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1027_, 0, v_a_1026_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1029_ = l_Lean_Core_mkFreshUserName(v___x_1028_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4, &l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4);
v___x_1033_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1030_, v___x_1032_, v___f_1027_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
lean_inc_ref(v_resultType_1011_);
v___x_1035_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1010_, v_resultType_1011_, v___f_1012_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v_doBlockResultType_1037_; lean_object* v___x_1038_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v_doBlockResultType_1037_ = lean_ctor_get(v___y_1015_, 3);
lean_inc_ref(v_doBlockResultType_1037_);
v___x_1038_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1037_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1052_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_u_1043_; lean_object* v_v_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_u_1043_ = lean_ctor_get(v_baseMonadInfo_1013_, 1);
v_v_1044_ = lean_ctor_get(v_baseMonadInfo_1013_, 2);
lean_inc(v_v_1044_);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_v_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1031_);
lean_inc(v_u_1043_);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_u_1043_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_mkConst(v_casesOnWrapper_1014_, v___x_1046_);
v___x_1048_ = l_Lean_mkApp5(v___x_1047_, v_resultType_1011_, v_a_1039_, v_a_1024_, v_a_1034_, v_a_1036_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1048_);
v___x_1050_ = v___x_1041_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_dec(v_a_1036_);
lean_dec(v_a_1034_);
lean_dec(v_a_1024_);
lean_dec(v_casesOnWrapper_1014_);
lean_dec_ref(v_resultType_1011_);
return v___x_1038_;
}
}
else
{
lean_dec(v_a_1034_);
lean_dec(v_a_1024_);
lean_dec(v_casesOnWrapper_1014_);
lean_dec_ref(v_resultType_1011_);
return v___x_1035_;
}
}
else
{
lean_dec(v_a_1024_);
lean_dec(v_casesOnWrapper_1014_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v_resultType_1011_);
lean_dec(v_resultName_1010_);
return v___x_1033_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v___f_1027_);
lean_dec(v_a_1024_);
lean_dec(v_casesOnWrapper_1014_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v_resultType_1011_);
lean_dec(v_resultName_1010_);
v_a_1053_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1029_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1029_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1024_);
lean_dec(v_casesOnWrapper_1014_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v_resultType_1011_);
lean_dec(v_resultName_1010_);
v_a_1061_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1025_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1025_);
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
lean_dec(v_casesOnWrapper_1014_);
lean_dec_ref(v___f_1012_);
lean_dec_ref(v_resultType_1011_);
lean_dec(v_resultName_1010_);
lean_dec_ref(v_getCont_1009_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object* v_a_1069_, lean_object* v_getCont_1070_, lean_object* v_resultName_1071_, lean_object* v_resultType_1072_, lean_object* v___f_1073_, lean_object* v_baseMonadInfo_1074_, lean_object* v_casesOnWrapper_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1069_, v_getCont_1070_, v_resultName_1071_, v_resultType_1072_, v___f_1073_, v_baseMonadInfo_1074_, v_casesOnWrapper_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_baseMonadInfo_1074_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object* v_getCont_1088_, lean_object* v_baseMonadInfo_1089_, lean_object* v_casesOnWrapper_1090_, lean_object* v_restoreCont_1091_, lean_object* v_dec_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_inc_ref(v_dec_1092_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1101_, 0, v_dec_1092_);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1103_ = l_Lean_Core_mkFreshUserName(v___x_1102_, v___y_1098_, v___y_1099_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v_resultName_1105_; lean_object* v_resultType_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1117_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v_resultName_1105_ = lean_ctor_get(v_dec_1092_, 0);
v_resultType_1106_ = lean_ctor_get(v_dec_1092_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_dec_1092_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_dec_1092_, 2);
lean_dec(v_unused_1118_);
v___x_1108_ = v_dec_1092_;
v_isShared_1109_ = v_isSharedCheck_1117_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_resultType_1106_);
lean_inc(v_resultName_1105_);
lean_dec(v_dec_1092_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1117_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___f_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1114_; 
lean_inc_ref(v_baseMonadInfo_1089_);
lean_inc_ref(v_resultType_1106_);
lean_inc(v_a_1104_);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed), 15, 7);
lean_closure_set(v___f_1110_, 0, v_a_1104_);
lean_closure_set(v___f_1110_, 1, v_getCont_1088_);
lean_closure_set(v___f_1110_, 2, v_resultName_1105_);
lean_closure_set(v___f_1110_, 3, v_resultType_1106_);
lean_closure_set(v___f_1110_, 4, v___f_1101_);
lean_closure_set(v___f_1110_, 5, v_baseMonadInfo_1089_);
lean_closure_set(v___f_1110_, 6, v_casesOnWrapper_1090_);
v___x_1111_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1089_, v_resultType_1106_);
lean_dec_ref(v_baseMonadInfo_1089_);
v___x_1112_ = 0;
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 2, v___f_1110_);
lean_ctor_set(v___x_1108_, 1, v___x_1111_);
lean_ctor_set(v___x_1108_, 0, v_a_1104_);
v___x_1114_ = v___x_1108_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v___f_1110_);
v___x_1114_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; 
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*3, v___x_1112_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
lean_inc_ref(v___y_1093_);
v___x_1115_ = lean_apply_9(v_restoreCont_1091_, v___x_1114_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v___f_1101_);
lean_dec_ref(v_dec_1092_);
lean_dec_ref(v_restoreCont_1091_);
lean_dec(v_casesOnWrapper_1090_);
lean_dec_ref(v_baseMonadInfo_1089_);
lean_dec_ref(v_getCont_1088_);
v_a_1119_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1103_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1103_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object* v_getCont_1127_, lean_object* v_baseMonadInfo_1128_, lean_object* v_casesOnWrapper_1129_, lean_object* v_restoreCont_1130_, lean_object* v_dec_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1127_, v_baseMonadInfo_1128_, v_casesOnWrapper_1129_, v_restoreCont_1130_, v_dec_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object* v_baseMonadInfo_1141_, lean_object* v_stM_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1141_, v___y_1143_);
lean_inc(v___y_1150_);
lean_inc_ref(v___y_1149_);
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc_ref(v___y_1144_);
v___x_1153_ = lean_apply_9(v_stM_1142_, v___x_1152_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, lean_box(0));
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object* v_baseMonadInfo_1154_, lean_object* v_stM_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1154_, v_stM_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_baseMonadInfo_1154_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object* v_m_1166_, lean_object* v_baseMonadInfo_1167_, lean_object* v_optionTWrapper_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc_ref(v___y_1169_);
v___x_1177_ = lean_apply_8(v_m_1166_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, lean_box(0));
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1192_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1192_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1192_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_u_1182_; lean_object* v_v_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v_u_1182_ = lean_ctor_get(v_baseMonadInfo_1167_, 1);
v_v_1183_ = lean_ctor_get(v_baseMonadInfo_1167_, 2);
v___x_1184_ = lean_box(0);
lean_inc(v_v_1183_);
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_v_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
lean_inc(v_u_1182_);
v___x_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_u_1182_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = l_Lean_mkConst(v_optionTWrapper_1168_, v___x_1186_);
v___x_1188_ = l_Lean_Expr_app___override(v___x_1187_, v_a_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1188_);
v___x_1190_ = v___x_1180_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_dec(v_optionTWrapper_1168_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object* v_m_1193_, lean_object* v_baseMonadInfo_1194_, lean_object* v_optionTWrapper_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1193_, v_baseMonadInfo_1194_, v_optionTWrapper_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_baseMonadInfo_1194_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object* v_baseMonadInfo_1205_, lean_object* v_optionTWrapper_1206_, lean_object* v_casesOnWrapper_1207_, lean_object* v_getCont_1208_, lean_object* v_base_1209_){
_start:
{
lean_object* v_description_1210_; lean_object* v_m_1211_; lean_object* v_stM_1212_; lean_object* v_runInBase_1213_; lean_object* v_restoreCont_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1226_; 
v_description_1210_ = lean_ctor_get(v_base_1209_, 0);
v_m_1211_ = lean_ctor_get(v_base_1209_, 1);
v_stM_1212_ = lean_ctor_get(v_base_1209_, 2);
v_runInBase_1213_ = lean_ctor_get(v_base_1209_, 3);
v_restoreCont_1214_ = lean_ctor_get(v_base_1209_, 4);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_base_1209_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1216_ = v_base_1209_;
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_restoreCont_1214_);
lean_inc(v_runInBase_1213_);
lean_inc(v_stM_1212_);
lean_inc(v_m_1211_);
lean_inc(v_description_1210_);
lean_dec(v_base_1209_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1226_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___x_1224_; 
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1218_, 0, v_runInBase_1213_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1), 2, 1);
lean_closure_set(v___f_1219_, 0, v_description_1210_);
lean_inc_ref_n(v_baseMonadInfo_1205_, 2);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed), 13, 4);
lean_closure_set(v___f_1220_, 0, v_getCont_1208_);
lean_closure_set(v___f_1220_, 1, v_baseMonadInfo_1205_);
lean_closure_set(v___f_1220_, 2, v_casesOnWrapper_1207_);
lean_closure_set(v___f_1220_, 3, v_restoreCont_1214_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed), 11, 2);
lean_closure_set(v___f_1221_, 0, v_baseMonadInfo_1205_);
lean_closure_set(v___f_1221_, 1, v_stM_1212_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed), 11, 3);
lean_closure_set(v___f_1222_, 0, v_m_1211_);
lean_closure_set(v___f_1222_, 1, v_baseMonadInfo_1205_);
lean_closure_set(v___f_1222_, 2, v_optionTWrapper_1206_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 4, v___f_1220_);
lean_ctor_set(v___x_1216_, 3, v___f_1218_);
lean_ctor_set(v___x_1216_, 2, v___f_1221_);
lean_ctor_set(v___x_1216_, 1, v___f_1222_);
lean_ctor_set(v___x_1216_, 0, v___f_1219_);
v___x_1224_ = v___x_1216_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___f_1219_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___f_1222_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v___f_1221_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v___f_1218_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v___f_1220_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object* v_00_u03b1_1227_, lean_object* v_name_1228_, uint8_t v_bi_1229_, lean_object* v_type_1230_, lean_object* v_k_1231_, uint8_t v_kind_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_1228_, v_bi_1229_, v_type_1230_, v_k_1231_, v_kind_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_name_1243_, lean_object* v_bi_1244_, lean_object* v_type_1245_, lean_object* v_k_1246_, lean_object* v_kind_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_bi_boxed_1256_; uint8_t v_kind_boxed_1257_; lean_object* v_res_1258_; 
v_bi_boxed_1256_ = lean_unbox(v_bi_1244_);
v_kind_boxed_1257_ = lean_unbox(v_kind_1247_);
v_res_1258_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_1242_, v_name_1243_, v_bi_boxed_1256_, v_type_1245_, v_k_1246_, v_kind_boxed_1257_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object* v_00_u03b1_1259_, lean_object* v_name_1260_, lean_object* v_type_1261_, lean_object* v_k_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1260_, v_type_1261_, v_k_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_name_1273_, lean_object* v_type_1274_, lean_object* v_k_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(v_00_u03b1_1272_, v_name_1273_, v_type_1274_, v_k_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object* v_baseMonadInfo_1288_, lean_object* v_getCont_1289_, lean_object* v_00_u03b1_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; 
lean_inc(v_a_1297_);
lean_inc_ref(v_a_1296_);
lean_inc(v_a_1295_);
lean_inc_ref(v_a_1294_);
lean_inc(v_a_1293_);
lean_inc_ref(v_a_1292_);
lean_inc_ref(v_a_1291_);
v___x_1299_ = lean_apply_8(v_getCont_1289_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, lean_box(0));
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1322_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1322_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1322_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_u_1304_; lean_object* v_resultType_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1320_; 
v_u_1304_ = lean_ctor_get(v_baseMonadInfo_1288_, 1);
v_resultType_1305_ = lean_ctor_get(v_a_1300_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1300_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v_a_1300_, 1);
lean_dec(v_unused_1321_);
v___x_1307_ = v_a_1300_;
v_isShared_1308_ = v_isSharedCheck_1320_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_resultType_1305_);
lean_dec(v_a_1300_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1320_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(0);
lean_inc(v_u_1304_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 1);
lean_ctor_set(v___x_1307_, 1, v___x_1309_);
lean_ctor_set(v___x_1307_, 0, v_u_1304_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_u_1304_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
lean_inc(v_u_1304_);
v___x_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_u_1304_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
v___x_1314_ = l_Lean_mkConst(v___x_1312_, v___x_1313_);
v___x_1315_ = l_Lean_mkAppB(v___x_1314_, v_resultType_1305_, v_00_u03b1_1290_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1315_);
v___x_1317_ = v___x_1302_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v_00_u03b1_1290_);
v_a_1323_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1299_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1299_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object* v_baseMonadInfo_1331_, lean_object* v_getCont_1332_, lean_object* v_00_u03b1_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1331_, v_getCont_1332_, v_00_u03b1_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec_ref(v_baseMonadInfo_1331_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object* v_dec_1343_, lean_object* v_r_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_k_1353_; lean_object* v___x_1354_; 
v_k_1353_ = lean_ctor_get(v_dec_1343_, 2);
lean_inc_ref(v_k_1353_);
lean_dec_ref(v_dec_1343_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc_ref(v___y_1345_);
v___x_1354_ = lean_apply_8(v_k_1353_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_n(v_a_1355_, 2);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_mk_empty_array_with_capacity(v___x_1356_);
v___x_1358_ = lean_array_push(v___x_1357_, v_r_1344_);
v___x_1359_ = 0;
v___x_1360_ = 1;
v___x_1361_ = 1;
v___x_1362_ = l_Lean_Meta_mkLambdaFVars(v___x_1358_, v_a_1355_, v___x_1359_, v___x_1360_, v___x_1359_, v___x_1360_, v___x_1361_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec_ref(v___x_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1364_ = lean_infer_type(v_a_1355_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1373_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1363_);
lean_ctor_set(v___x_1369_, 1, v_a_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1363_);
v_a_1374_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1364_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1364_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1355_);
v_a_1382_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1362_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1362_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_r_1344_);
v_a_1390_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1354_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1354_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object* v_dec_1398_, lean_object* v_r_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_dec_1398_, v_r_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object* v_a_1409_, lean_object* v_r_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_k_1419_; lean_object* v___x_1420_; 
v_k_1419_ = lean_ctor_get(v_a_1409_, 1);
lean_inc_ref(v_k_1419_);
lean_dec_ref(v_a_1409_);
lean_inc(v___y_1417_);
lean_inc_ref(v___y_1416_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc_ref(v_r_1410_);
v___x_1420_ = lean_apply_9(v_k_1419_, v_r_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, lean_box(0));
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_mk_empty_array_with_capacity(v___x_1422_);
v___x_1424_ = lean_array_push(v___x_1423_, v_r_1410_);
v___x_1425_ = 0;
v___x_1426_ = 1;
v___x_1427_ = 1;
v___x_1428_ = l_Lean_Meta_mkLambdaFVars(v___x_1424_, v_a_1421_, v___x_1425_, v___x_1426_, v___x_1425_, v___x_1426_, v___x_1427_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec_ref(v___x_1424_);
return v___x_1428_;
}
else
{
lean_dec_ref(v_r_1410_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object* v_a_1429_, lean_object* v_r_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_a_1429_, v_r_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object* v_a_1440_, lean_object* v_getCont_1441_, lean_object* v_resultName_1442_, lean_object* v_resultType_1443_, lean_object* v___f_1444_, lean_object* v_baseMonadInfo_1445_, lean_object* v_casesOnWrapper_1446_, lean_object* v_00_u03b5_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Meta_getFVarFromUserName(v_a_1440_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc_ref(v___y_1448_);
v___x_1458_ = lean_apply_8(v_getCont_1441_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, lean_box(0));
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc_n(v_a_1459_, 2);
lean_dec_ref_known(v___x_1458_, 1);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1460_, 0, v_a_1459_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1462_ = l_Lean_Core_mkFreshUserName(v___x_1461_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_resultType_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1504_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v_resultType_1464_ = lean_ctor_get(v_a_1459_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_a_1459_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v_a_1459_, 1);
lean_dec(v_unused_1505_);
v___x_1466_ = v_a_1459_;
v_isShared_1467_ = v_isSharedCheck_1504_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_resultType_1464_);
lean_dec(v_a_1459_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1504_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1463_, v_resultType_1464_, v___f_1460_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
lean_inc_ref(v_resultType_1443_);
v___x_1470_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1442_, v_resultType_1443_, v___f_1444_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1495_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1495_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1495_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1494_; 
v_fst_1475_ = lean_ctor_get(v_a_1471_, 0);
v_snd_1476_ = lean_ctor_get(v_a_1471_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1478_ = v_a_1471_;
v_isShared_1479_ = v_isSharedCheck_1494_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_snd_1476_);
lean_inc(v_fst_1475_);
lean_dec(v_a_1471_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1494_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_u_1480_; lean_object* v_v_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v_u_1480_ = lean_ctor_get(v_baseMonadInfo_1445_, 1);
v_v_1481_ = lean_ctor_get(v_baseMonadInfo_1445_, 2);
v___x_1482_ = lean_box(0);
lean_inc(v_v_1481_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 1);
lean_ctor_set(v___x_1478_, 1, v___x_1482_);
lean_ctor_set(v___x_1478_, 0, v_v_1481_);
v___x_1484_ = v___x_1478_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_v_1481_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
lean_inc(v_u_1480_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 1);
lean_ctor_set(v___x_1466_, 1, v___x_1484_);
lean_ctor_set(v___x_1466_, 0, v_u_1480_);
v___x_1486_ = v___x_1466_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_u_1480_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1487_ = l_Lean_mkConst(v_casesOnWrapper_1446_, v___x_1486_);
v___x_1488_ = l_Lean_mkApp6(v___x_1487_, v_00_u03b5_1447_, v_resultType_1443_, v_snd_1476_, v_a_1457_, v_a_1469_, v_fst_1475_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1488_);
v___x_1490_ = v___x_1473_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1469_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1457_);
lean_dec_ref(v_00_u03b5_1447_);
lean_dec(v_casesOnWrapper_1446_);
lean_dec_ref(v_resultType_1443_);
v_a_1496_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1470_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1470_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_del_object(v___x_1466_);
lean_dec(v_a_1457_);
lean_dec_ref(v_00_u03b5_1447_);
lean_dec(v_casesOnWrapper_1446_);
lean_dec_ref(v___f_1444_);
lean_dec_ref(v_resultType_1443_);
lean_dec(v_resultName_1442_);
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v___f_1460_);
lean_dec(v_a_1459_);
lean_dec(v_a_1457_);
lean_dec_ref(v_00_u03b5_1447_);
lean_dec(v_casesOnWrapper_1446_);
lean_dec_ref(v___f_1444_);
lean_dec_ref(v_resultType_1443_);
lean_dec(v_resultName_1442_);
v_a_1506_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1462_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1462_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_a_1457_);
lean_dec_ref(v_00_u03b5_1447_);
lean_dec(v_casesOnWrapper_1446_);
lean_dec_ref(v___f_1444_);
lean_dec_ref(v_resultType_1443_);
lean_dec(v_resultName_1442_);
v_a_1514_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1458_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1458_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1447_);
lean_dec(v_casesOnWrapper_1446_);
lean_dec_ref(v___f_1444_);
lean_dec_ref(v_resultType_1443_);
lean_dec(v_resultName_1442_);
lean_dec_ref(v_getCont_1441_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object* v_a_1522_, lean_object* v_getCont_1523_, lean_object* v_resultName_1524_, lean_object* v_resultType_1525_, lean_object* v___f_1526_, lean_object* v_baseMonadInfo_1527_, lean_object* v_casesOnWrapper_1528_, lean_object* v_00_u03b5_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1522_, v_getCont_1523_, v_resultName_1524_, v_resultType_1525_, v___f_1526_, v_baseMonadInfo_1527_, v_casesOnWrapper_1528_, v_00_u03b5_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_baseMonadInfo_1527_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object* v_getCont_1539_, lean_object* v_baseMonadInfo_1540_, lean_object* v_casesOnWrapper_1541_, lean_object* v_00_u03b5_1542_, lean_object* v_restoreCont_1543_, lean_object* v_dec_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_inc_ref(v_dec_1544_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1553_, 0, v_dec_1544_);
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1555_ = l_Lean_Core_mkFreshUserName(v___x_1554_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v_resultName_1557_; lean_object* v_resultType_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1578_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_resultName_1557_ = lean_ctor_get(v_dec_1544_, 0);
v_resultType_1558_ = lean_ctor_get(v_dec_1544_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_dec_1544_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_dec_1544_, 2);
lean_dec(v_unused_1579_);
v___x_1560_ = v_dec_1544_;
v_isShared_1561_ = v_isSharedCheck_1578_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_resultType_1558_);
lean_inc(v_resultName_1557_);
lean_dec(v_dec_1544_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1578_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___f_1562_; lean_object* v___x_1563_; 
lean_inc_ref(v_baseMonadInfo_1540_);
lean_inc_ref(v_resultType_1558_);
lean_inc_ref(v_getCont_1539_);
lean_inc(v_a_1556_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed), 16, 8);
lean_closure_set(v___f_1562_, 0, v_a_1556_);
lean_closure_set(v___f_1562_, 1, v_getCont_1539_);
lean_closure_set(v___f_1562_, 2, v_resultName_1557_);
lean_closure_set(v___f_1562_, 3, v_resultType_1558_);
lean_closure_set(v___f_1562_, 4, v___f_1553_);
lean_closure_set(v___f_1562_, 5, v_baseMonadInfo_1540_);
lean_closure_set(v___f_1562_, 6, v_casesOnWrapper_1541_);
lean_closure_set(v___f_1562_, 7, v_00_u03b5_1542_);
v___x_1563_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1540_, v_getCont_1539_, v_resultType_1558_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v_baseMonadInfo_1540_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; uint8_t v___x_1565_; lean_object* v___x_1567_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = 0;
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 2, v___f_1562_);
lean_ctor_set(v___x_1560_, 1, v_a_1564_);
lean_ctor_set(v___x_1560_, 0, v_a_1556_);
v___x_1567_ = v___x_1560_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1556_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_a_1564_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v___f_1562_);
v___x_1567_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*3, v___x_1565_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc_ref(v___y_1546_);
lean_inc_ref(v___y_1545_);
v___x_1568_ = lean_apply_9(v_restoreCont_1543_, v___x_1567_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, lean_box(0));
return v___x_1568_;
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v___f_1562_);
lean_del_object(v___x_1560_);
lean_dec(v_a_1556_);
lean_dec_ref(v_restoreCont_1543_);
v_a_1570_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1563_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1563_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___f_1553_);
lean_dec_ref(v_dec_1544_);
lean_dec_ref(v_restoreCont_1543_);
lean_dec_ref(v_00_u03b5_1542_);
lean_dec(v_casesOnWrapper_1541_);
lean_dec_ref(v_baseMonadInfo_1540_);
lean_dec_ref(v_getCont_1539_);
v_a_1580_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1555_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1555_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object* v_getCont_1588_, lean_object* v_baseMonadInfo_1589_, lean_object* v_casesOnWrapper_1590_, lean_object* v_00_u03b5_1591_, lean_object* v_restoreCont_1592_, lean_object* v_dec_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_getCont_1588_, v_baseMonadInfo_1589_, v_casesOnWrapper_1590_, v_00_u03b5_1591_, v_restoreCont_1592_, v_dec_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2));
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object* v_00_u03b5_1609_, lean_object* v_description_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1612_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1);
v___x_1613_ = l_Lean_MessageData_ofExpr(v_00_u03b5_1609_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_apply_1(v_description_1610_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object* v_baseMonadInfo_1620_, lean_object* v_getCont_1621_, lean_object* v_stM_1622_, lean_object* v_00_u03b1_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1620_, v_getCont_1621_, v_00_u03b1_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc_ref(v___y_1624_);
v___x_1634_ = lean_apply_9(v_stM_1622_, v_a_1633_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, lean_box(0));
return v___x_1634_;
}
else
{
lean_dec_ref(v_stM_1622_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object* v_baseMonadInfo_1635_, lean_object* v_getCont_1636_, lean_object* v_stM_1637_, lean_object* v_00_u03b1_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1635_, v_getCont_1636_, v_stM_1637_, v_00_u03b1_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v_baseMonadInfo_1635_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object* v_runInBase_1652_, lean_object* v_e_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1));
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_mk_empty_array_with_capacity(v___x_1663_);
v___x_1665_ = lean_array_push(v___x_1664_, v_e_1653_);
v___x_1666_ = l_Lean_Meta_mkAppM(v___x_1662_, v___x_1665_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc_ref(v___y_1654_);
v___x_1668_ = lean_apply_9(v_runInBase_1652_, v_a_1667_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1668_;
}
else
{
lean_dec_ref(v_runInBase_1652_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object* v_runInBase_1669_, lean_object* v_e_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1669_, v_e_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object* v_m_1680_, lean_object* v_baseMonadInfo_1681_, lean_object* v_exceptTWrapper_1682_, lean_object* v_00_u03b5_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1692_ = lean_apply_8(v_m_1680_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, lean_box(0));
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1707_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1707_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1707_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_u_1697_; lean_object* v_v_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v_u_1697_ = lean_ctor_get(v_baseMonadInfo_1681_, 1);
v_v_1698_ = lean_ctor_get(v_baseMonadInfo_1681_, 2);
v___x_1699_ = lean_box(0);
lean_inc(v_v_1698_);
v___x_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_v_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
lean_inc(v_u_1697_);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_u_1697_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_mkConst(v_exceptTWrapper_1682_, v___x_1701_);
v___x_1703_ = l_Lean_mkAppB(v___x_1702_, v_00_u03b5_1683_, v_a_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1703_);
v___x_1705_ = v___x_1695_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1683_);
lean_dec(v_exceptTWrapper_1682_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object* v_m_1708_, lean_object* v_baseMonadInfo_1709_, lean_object* v_exceptTWrapper_1710_, lean_object* v_00_u03b5_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1708_, v_baseMonadInfo_1709_, v_exceptTWrapper_1710_, v_00_u03b5_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec_ref(v_baseMonadInfo_1709_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object* v_baseMonadInfo_1721_, lean_object* v_exceptTWrapper_1722_, lean_object* v_casesOnWrapper_1723_, lean_object* v_getCont_1724_, lean_object* v_00_u03b5_1725_, lean_object* v_base_1726_){
_start:
{
lean_object* v_description_1727_; lean_object* v_m_1728_; lean_object* v_stM_1729_; lean_object* v_runInBase_1730_; lean_object* v_restoreCont_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1743_; 
v_description_1727_ = lean_ctor_get(v_base_1726_, 0);
v_m_1728_ = lean_ctor_get(v_base_1726_, 1);
v_stM_1729_ = lean_ctor_get(v_base_1726_, 2);
v_runInBase_1730_ = lean_ctor_get(v_base_1726_, 3);
v_restoreCont_1731_ = lean_ctor_get(v_base_1726_, 4);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_base_1726_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1733_ = v_base_1726_;
v_isShared_1734_ = v_isSharedCheck_1743_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_restoreCont_1731_);
lean_inc(v_runInBase_1730_);
lean_inc(v_stM_1729_);
lean_inc(v_m_1728_);
lean_inc(v_description_1727_);
lean_dec(v_base_1726_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1743_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v___f_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1741_; 
lean_inc_ref_n(v_00_u03b5_1725_, 2);
lean_inc_ref_n(v_baseMonadInfo_1721_, 2);
lean_inc_ref(v_getCont_1724_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed), 14, 5);
lean_closure_set(v___f_1735_, 0, v_getCont_1724_);
lean_closure_set(v___f_1735_, 1, v_baseMonadInfo_1721_);
lean_closure_set(v___f_1735_, 2, v_casesOnWrapper_1723_);
lean_closure_set(v___f_1735_, 3, v_00_u03b5_1725_);
lean_closure_set(v___f_1735_, 4, v_restoreCont_1731_);
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4), 3, 2);
lean_closure_set(v___f_1736_, 0, v_00_u03b5_1725_);
lean_closure_set(v___f_1736_, 1, v_description_1727_);
v___f_1737_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed), 12, 3);
lean_closure_set(v___f_1737_, 0, v_baseMonadInfo_1721_);
lean_closure_set(v___f_1737_, 1, v_getCont_1724_);
lean_closure_set(v___f_1737_, 2, v_stM_1729_);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed), 10, 1);
lean_closure_set(v___f_1738_, 0, v_runInBase_1730_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed), 12, 4);
lean_closure_set(v___f_1739_, 0, v_m_1728_);
lean_closure_set(v___f_1739_, 1, v_baseMonadInfo_1721_);
lean_closure_set(v___f_1739_, 2, v_exceptTWrapper_1722_);
lean_closure_set(v___f_1739_, 3, v_00_u03b5_1725_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 4, v___f_1735_);
lean_ctor_set(v___x_1733_, 3, v___f_1738_);
lean_ctor_set(v___x_1733_, 2, v___f_1737_);
lean_ctor_set(v___x_1733_, 1, v___f_1739_);
lean_ctor_set(v___x_1733_, 0, v___f_1736_);
v___x_1741_ = v___x_1733_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___f_1736_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___f_1739_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v___f_1737_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v___f_1738_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v___f_1735_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object* v_baseMonadInfo_1753_, lean_object* v_00_u03c1_1754_, lean_object* v_m_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1));
v___x_1757_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4));
v___x_1758_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5));
v___x_1759_ = l_Lean_Elab_Do_ControlStack_exceptT(v_baseMonadInfo_1753_, v___x_1756_, v___x_1757_, v___x_1758_, v_00_u03c1_1754_, v_m_1755_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_1763_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1782_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1774_);
v___x_1776_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1);
v___x_1777_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1776_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; lean_object* v___x_1780_; 
v_val_1778_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v_a_1772_, 1);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v_val_1778_);
v___x_1780_ = v___x_1774_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_val_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1771_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1771_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object* v_baseMonadInfo_1808_, lean_object* v_m_1809_){
_start:
{
lean_object* v_getCont_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_getCont_1810_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__0));
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__2));
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__4));
v___x_1813_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1808_, v___x_1811_, v___x_1812_, v_getCont_1810_, v_m_1809_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_1817_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1836_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
if (lean_obj_tag(v_a_1826_) == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1828_);
v___x_1830_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1);
v___x_1831_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1830_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1831_;
}
else
{
lean_object* v_val_1832_; lean_object* v___x_1834_; 
v_val_1832_ = lean_ctor_get(v_a_1826_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v_a_1826_, 1);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v_val_1832_);
v___x_1834_ = v___x_1828_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_val_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_a_1837_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1825_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1825_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object* v_baseMonadInfo_1862_, lean_object* v_m_1863_){
_start:
{
lean_object* v_getCont_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_getCont_1864_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__0));
v___x_1865_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__2));
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__4));
v___x_1867_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1862_, v___x_1865_, v___x_1866_, v_getCont_1864_, v_m_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object* v_mi_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_m_1879_; lean_object* v_u_1880_; lean_object* v_v_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_m_1879_ = lean_ctor_get(v_mi_1871_, 0);
lean_inc_ref(v_m_1879_);
v_u_1880_ = lean_ctor_get(v_mi_1871_, 1);
lean_inc(v_u_1880_);
v_v_1881_ = lean_ctor_get(v_mi_1871_, 2);
lean_inc(v_v_1881_);
lean_dec_ref(v_mi_1871_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1));
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_v_1881_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_u_1880_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_mkConst(v___x_1882_, v___x_1885_);
v___x_1887_ = l_Lean_Expr_app___override(v___x_1886_, v_m_1879_);
v___x_1888_ = lean_box(0);
v___x_1889_ = l_Lean_Elab_Term_mkInstMVar(v___x_1887_, v___x_1888_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object* v_mi_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
return v_res_1898_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0));
v___x_1901_ = l_Lean_stringToMessageData(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6));
v___x_1910_ = l_Lean_stringToMessageData(v___x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object* v_msg_1911_, lean_object* v_expected_1912_, lean_object* v_actual_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; 
lean_inc_ref(v_actual_1913_);
lean_inc_ref(v_expected_1912_);
v___x_1919_ = l_Lean_Meta_isExprDefEq(v_expected_1912_, v_actual_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1943_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1943_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1943_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_unbox(v_a_1920_);
lean_dec(v_a_1920_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1922_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
v___x_1926_ = l_Lean_stringToMessageData(v_msg_1911_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_MessageData_ofExpr(v_expected_1912_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = l_Lean_MessageData_ofExpr(v_actual_1913_);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1937_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_dec_ref(v_actual_1913_);
lean_dec_ref(v_expected_1912_);
lean_dec_ref(v_msg_1911_);
v___x_1939_ = lean_box(0);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1939_);
v___x_1941_ = v___x_1922_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
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
lean_dec_ref(v_actual_1913_);
lean_dec_ref(v_expected_1912_);
lean_dec_ref(v_msg_1911_);
v_a_1944_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1919_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1919_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object* v_msg_1952_, lean_object* v_expected_1953_, lean_object* v_actual_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1952_, v_expected_1953_, v_actual_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object* v_msg_1961_, lean_object* v_expected_1962_, lean_object* v_actual_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1961_, v_expected_1962_, v_actual_1963_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object* v_msg_1973_, lean_object* v_expected_1974_, lean_object* v_actual_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_1973_, v_expected_1974_, v_actual_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object* v_base_1990_, uint8_t v_hasContinue_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_m_2000_; lean_object* v_runInBase_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2059_; 
v_m_2000_ = lean_ctor_get(v_base_1990_, 1);
v_runInBase_2001_ = lean_ctor_get(v_base_1990_, 3);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_base_1990_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; lean_object* v_unused_2061_; lean_object* v_unused_2062_; 
v_unused_2060_ = lean_ctor_get(v_base_1990_, 4);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_base_1990_, 2);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_base_1990_, 0);
lean_dec(v_unused_2062_);
v___x_2003_ = v_base_1990_;
v_isShared_2004_ = v_isSharedCheck_2059_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_runInBase_2001_);
lean_inc(v_m_2000_);
lean_dec(v_base_1990_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2059_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; 
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
lean_inc_ref(v_a_1992_);
v___x_2005_ = lean_apply_8(v_m_2000_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, lean_box(0));
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_monadInfo_2006_; lean_object* v_a_2007_; lean_object* v_doBlockResultType_2008_; lean_object* v_u_2009_; lean_object* v_v_2010_; lean_object* v_cachedPUnit_2011_; lean_object* v_cachedPUnitUnit_2012_; lean_object* v___x_2014_; 
v_monadInfo_2006_ = lean_ctor_get(v_a_1992_, 0);
v_a_2007_ = lean_ctor_get(v___x_2005_, 0);
lean_inc_n(v_a_2007_, 2);
lean_dec_ref_known(v___x_2005_, 1);
v_doBlockResultType_2008_ = lean_ctor_get(v_a_1992_, 3);
v_u_2009_ = lean_ctor_get(v_monadInfo_2006_, 1);
v_v_2010_ = lean_ctor_get(v_monadInfo_2006_, 2);
v_cachedPUnit_2011_ = lean_ctor_get(v_monadInfo_2006_, 3);
v_cachedPUnitUnit_2012_ = lean_ctor_get(v_monadInfo_2006_, 4);
lean_inc_ref(v_cachedPUnitUnit_2012_);
lean_inc_ref(v_cachedPUnit_2011_);
lean_inc(v_v_2010_);
lean_inc(v_u_2009_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v_cachedPUnitUnit_2012_);
lean_ctor_set(v___x_2003_, 3, v_cachedPUnit_2011_);
lean_ctor_set(v___x_2003_, 2, v_v_2010_);
lean_ctor_set(v___x_2003_, 1, v_u_2009_);
lean_ctor_set(v___x_2003_, 0, v_a_2007_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_u_2009_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v_v_2010_);
lean_ctor_set(v_reuseFailAlloc_2058_, 3, v_cachedPUnit_2011_);
lean_ctor_set(v_reuseFailAlloc_2058_, 4, v_cachedPUnitUnit_2012_);
v___x_2014_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2014_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2018_ = 0;
v___x_2019_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2017_, v___x_2018_, v_a_1992_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___y_2022_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
if (v_hasContinue_1991_ == 0)
{
v___y_2022_ = v_a_2020_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_2054_ = lean_box(0);
lean_inc(v_u_2009_);
v___x_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_u_2009_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = l_Lean_mkConst(v___x_2053_, v___x_2055_);
v___x_2057_ = l_Lean_Expr_app___override(v___x_2056_, v_a_2020_);
v___y_2022_ = v___x_2057_;
goto v___jp_2021_;
}
v___jp_2021_:
{
lean_object* v___x_2023_; 
lean_inc_ref(v_doBlockResultType_2008_);
v___x_2023_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2008_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1));
v___x_2026_ = lean_box(0);
lean_inc(v_v_2010_);
v___x_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_v_2010_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
lean_inc(v_u_2009_);
v___x_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_u_2009_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l_Lean_mkConst(v___x_2025_, v___x_2028_);
v___x_2030_ = l_Lean_mkApp3(v___x_2029_, v___y_2022_, v_a_2007_, v_a_2016_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
lean_inc_ref(v_a_1992_);
v___x_2031_ = lean_apply_9(v_runInBase_2001_, v___x_2030_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, lean_box(0));
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_n(v_a_2032_, 2);
lean_dec_ref_known(v___x_2031_, 1);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
v___x_2033_ = lean_infer_type(v_a_2032_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2));
v___x_2036_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2035_, v_a_2024_, v_a_2034_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2044_);
v___x_2038_ = v___x_2036_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2036_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_a_2032_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2032_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2032_);
v_a_2045_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2036_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2036_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_dec(v_a_2032_);
lean_dec(v_a_2024_);
return v___x_2033_;
}
}
else
{
lean_dec(v_a_2024_);
return v___x_2031_;
}
}
else
{
lean_dec_ref(v___y_2022_);
lean_dec(v_a_2016_);
lean_dec(v_a_2007_);
lean_dec_ref(v_runInBase_2001_);
return v___x_2023_;
}
}
}
else
{
lean_dec(v_a_2016_);
lean_dec(v_a_2007_);
lean_dec_ref(v_runInBase_2001_);
return v___x_2019_;
}
}
else
{
lean_dec(v_a_2007_);
lean_dec_ref(v_runInBase_2001_);
return v___x_2015_;
}
}
}
else
{
lean_del_object(v___x_2003_);
lean_dec_ref(v_runInBase_2001_);
return v___x_2005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object* v_base_2063_, lean_object* v_hasContinue_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
uint8_t v_hasContinue_boxed_2073_; lean_object* v_res_2074_; 
v_hasContinue_boxed_2073_ = lean_unbox(v_hasContinue_2064_);
v_res_2074_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2063_, v_hasContinue_boxed_2073_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec_ref(v_a_2065_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object* v_base_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_m_2089_; lean_object* v_runInBase_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2141_; 
v_m_2089_ = lean_ctor_get(v_base_2080_, 1);
v_runInBase_2090_ = lean_ctor_get(v_base_2080_, 3);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_base_2080_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; lean_object* v_unused_2143_; lean_object* v_unused_2144_; 
v_unused_2142_ = lean_ctor_get(v_base_2080_, 4);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_base_2080_, 2);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_base_2080_, 0);
lean_dec(v_unused_2144_);
v___x_2092_ = v_base_2080_;
v_isShared_2093_ = v_isSharedCheck_2141_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_runInBase_2090_);
lean_inc(v_m_2089_);
lean_dec(v_base_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2141_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; 
lean_inc(v_a_2087_);
lean_inc_ref(v_a_2086_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc_ref(v_a_2082_);
lean_inc_ref(v_a_2081_);
v___x_2094_ = lean_apply_8(v_m_2089_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, lean_box(0));
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_monadInfo_2095_; lean_object* v_a_2096_; lean_object* v_doBlockResultType_2097_; lean_object* v_u_2098_; lean_object* v_v_2099_; lean_object* v_cachedPUnit_2100_; lean_object* v_cachedPUnitUnit_2101_; lean_object* v___x_2103_; 
v_monadInfo_2095_ = lean_ctor_get(v_a_2081_, 0);
v_a_2096_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_n(v_a_2096_, 2);
lean_dec_ref_known(v___x_2094_, 1);
v_doBlockResultType_2097_ = lean_ctor_get(v_a_2081_, 3);
v_u_2098_ = lean_ctor_get(v_monadInfo_2095_, 1);
v_v_2099_ = lean_ctor_get(v_monadInfo_2095_, 2);
v_cachedPUnit_2100_ = lean_ctor_get(v_monadInfo_2095_, 3);
v_cachedPUnitUnit_2101_ = lean_ctor_get(v_monadInfo_2095_, 4);
lean_inc_ref(v_cachedPUnitUnit_2101_);
lean_inc_ref(v_cachedPUnit_2100_);
lean_inc(v_v_2099_);
lean_inc(v_u_2098_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 4, v_cachedPUnitUnit_2101_);
lean_ctor_set(v___x_2092_, 3, v_cachedPUnit_2100_);
lean_ctor_set(v___x_2092_, 2, v_v_2099_);
lean_ctor_set(v___x_2092_, 1, v_u_2098_);
lean_ctor_set(v___x_2092_, 0, v_a_2096_);
v___x_2103_ = v___x_2092_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2096_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_u_2098_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_v_2099_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_cachedPUnit_2100_);
lean_ctor_set(v_reuseFailAlloc_2140_, 4, v_cachedPUnitUnit_2101_);
v___x_2103_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; 
v___x_2104_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2103_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2107_ = 0;
v___x_2108_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2106_, v___x_2107_, v_a_2081_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
lean_inc_ref(v_doBlockResultType_2097_);
v___x_2110_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2097_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1));
v___x_2113_ = lean_box(0);
lean_inc(v_v_2099_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_v_2099_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
lean_inc(v_u_2098_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_u_2098_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_mkConst(v___x_2112_, v___x_2115_);
v___x_2117_ = l_Lean_mkApp3(v___x_2116_, v_a_2109_, v_a_2096_, v_a_2105_);
lean_inc(v_a_2087_);
lean_inc_ref(v_a_2086_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc_ref(v_a_2082_);
lean_inc_ref(v_a_2081_);
v___x_2118_ = lean_apply_9(v_runInBase_2090_, v___x_2117_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, lean_box(0));
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_n(v_a_2119_, 2);
lean_dec_ref_known(v___x_2118_, 1);
lean_inc(v_a_2087_);
lean_inc_ref(v_a_2086_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
v___x_2120_ = lean_infer_type(v_a_2119_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2));
v___x_2123_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2122_, v_a_2111_, v_a_2121_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2131_);
v___x_2125_ = v___x_2123_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2123_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v_a_2119_);
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2119_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_a_2119_);
v_a_2132_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2123_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2123_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_dec(v_a_2119_);
lean_dec(v_a_2111_);
return v___x_2120_;
}
}
else
{
lean_dec(v_a_2111_);
return v___x_2118_;
}
}
else
{
lean_dec(v_a_2109_);
lean_dec(v_a_2105_);
lean_dec(v_a_2096_);
lean_dec_ref(v_runInBase_2090_);
return v___x_2110_;
}
}
else
{
lean_dec(v_a_2105_);
lean_dec(v_a_2096_);
lean_dec_ref(v_runInBase_2090_);
return v___x_2108_;
}
}
else
{
lean_dec(v_a_2096_);
lean_dec_ref(v_runInBase_2090_);
return v___x_2104_;
}
}
}
else
{
lean_del_object(v___x_2092_);
lean_dec_ref(v_runInBase_2090_);
return v___x_2094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object* v_base_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object* v_base_2163_, lean_object* v_r_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_m_2173_; lean_object* v_runInBase_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2220_; 
v_m_2173_ = lean_ctor_get(v_base_2163_, 1);
v_runInBase_2174_ = lean_ctor_get(v_base_2163_, 3);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_base_2163_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; lean_object* v_unused_2223_; 
v_unused_2221_ = lean_ctor_get(v_base_2163_, 4);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_base_2163_, 2);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_base_2163_, 0);
lean_dec(v_unused_2223_);
v___x_2176_ = v_base_2163_;
v_isShared_2177_ = v_isSharedCheck_2220_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_runInBase_2174_);
lean_inc(v_m_2173_);
lean_dec(v_base_2163_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2220_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; 
lean_inc(v_a_2171_);
lean_inc_ref(v_a_2170_);
lean_inc(v_a_2169_);
lean_inc_ref(v_a_2168_);
lean_inc(v_a_2167_);
lean_inc_ref(v_a_2166_);
lean_inc_ref(v_a_2165_);
v___x_2178_ = lean_apply_8(v_m_2173_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, lean_box(0));
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_monadInfo_2179_; lean_object* v_a_2180_; lean_object* v_doBlockResultType_2181_; lean_object* v_u_2182_; lean_object* v_v_2183_; lean_object* v_cachedPUnit_2184_; lean_object* v_cachedPUnitUnit_2185_; lean_object* v___x_2187_; 
v_monadInfo_2179_ = lean_ctor_get(v_a_2165_, 0);
v_a_2180_ = lean_ctor_get(v___x_2178_, 0);
lean_inc_n(v_a_2180_, 2);
lean_dec_ref_known(v___x_2178_, 1);
v_doBlockResultType_2181_ = lean_ctor_get(v_a_2165_, 3);
v_u_2182_ = lean_ctor_get(v_monadInfo_2179_, 1);
v_v_2183_ = lean_ctor_get(v_monadInfo_2179_, 2);
v_cachedPUnit_2184_ = lean_ctor_get(v_monadInfo_2179_, 3);
v_cachedPUnitUnit_2185_ = lean_ctor_get(v_monadInfo_2179_, 4);
lean_inc_ref(v_cachedPUnitUnit_2185_);
lean_inc_ref(v_cachedPUnit_2184_);
lean_inc(v_v_2183_);
lean_inc(v_u_2182_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 4, v_cachedPUnitUnit_2185_);
lean_ctor_set(v___x_2176_, 3, v_cachedPUnit_2184_);
lean_ctor_set(v___x_2176_, 2, v_v_2183_);
lean_ctor_set(v___x_2176_, 1, v_u_2182_);
lean_ctor_set(v___x_2176_, 0, v_a_2180_);
v___x_2187_ = v___x_2176_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2180_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_u_2182_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_cachedPUnit_2184_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_cachedPUnitUnit_2185_);
v___x_2187_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2187_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
lean_inc(v_a_2171_);
lean_inc_ref(v_a_2170_);
lean_inc(v_a_2169_);
lean_inc_ref(v_a_2168_);
lean_inc_ref(v_r_2164_);
v___x_2190_ = lean_infer_type(v_r_2164_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1));
v___x_2193_ = 0;
v___x_2194_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2192_, v___x_2193_, v_a_2165_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
lean_inc_ref(v_doBlockResultType_2181_);
v___x_2196_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2181_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
v___x_2199_ = lean_box(0);
lean_inc(v_v_2183_);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_v_2183_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
lean_inc(v_u_2182_);
v___x_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_u_2182_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_inc_ref(v___x_2201_);
v___x_2202_ = l_Lean_mkConst(v___x_2198_, v___x_2201_);
lean_inc(v_a_2195_);
lean_inc(v_a_2191_);
v___x_2203_ = l_Lean_mkAppB(v___x_2202_, v_a_2191_, v_a_2195_);
lean_inc(v_a_2180_);
v___x_2204_ = l_Lean_Expr_app___override(v_a_2180_, v___x_2203_);
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2));
v___x_2206_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2205_, v_a_2197_, v___x_2204_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref_known(v___x_2206_, 1);
v___x_2207_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4));
v___x_2208_ = l_Lean_mkConst(v___x_2207_, v___x_2201_);
v___x_2209_ = l_Lean_mkApp5(v___x_2208_, v_a_2191_, v_a_2180_, v_a_2195_, v_a_2189_, v_r_2164_);
lean_inc(v_a_2171_);
lean_inc_ref(v_a_2170_);
lean_inc(v_a_2169_);
lean_inc_ref(v_a_2168_);
lean_inc(v_a_2167_);
lean_inc_ref(v_a_2166_);
lean_inc_ref(v_a_2165_);
v___x_2210_ = lean_apply_9(v_runInBase_2174_, v___x_2209_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, lean_box(0));
return v___x_2210_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref_known(v___x_2201_, 2);
lean_dec(v_a_2195_);
lean_dec(v_a_2191_);
lean_dec(v_a_2189_);
lean_dec(v_a_2180_);
lean_dec_ref(v_runInBase_2174_);
lean_dec_ref(v_r_2164_);
v_a_2211_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2206_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2206_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_dec(v_a_2195_);
lean_dec(v_a_2191_);
lean_dec(v_a_2189_);
lean_dec(v_a_2180_);
lean_dec_ref(v_runInBase_2174_);
lean_dec_ref(v_r_2164_);
return v___x_2196_;
}
}
else
{
lean_dec(v_a_2191_);
lean_dec(v_a_2189_);
lean_dec(v_a_2180_);
lean_dec_ref(v_runInBase_2174_);
lean_dec_ref(v_r_2164_);
return v___x_2194_;
}
}
else
{
lean_dec(v_a_2189_);
lean_dec(v_a_2180_);
lean_dec_ref(v_runInBase_2174_);
lean_dec_ref(v_r_2164_);
return v___x_2190_;
}
}
else
{
lean_dec(v_a_2180_);
lean_dec_ref(v_runInBase_2174_);
lean_dec_ref(v_r_2164_);
return v___x_2188_;
}
}
}
else
{
lean_del_object(v___x_2176_);
lean_dec_ref(v_runInBase_2174_);
lean_dec_ref(v_r_2164_);
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object* v_base_2224_, lean_object* v_r_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2224_, v_r_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object* v_base_2249_, lean_object* v_resultName_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_m_2259_; lean_object* v_runInBase_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2293_; 
v_m_2259_ = lean_ctor_get(v_base_2249_, 1);
v_runInBase_2260_ = lean_ctor_get(v_base_2249_, 3);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_base_2249_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2294_ = lean_ctor_get(v_base_2249_, 4);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_base_2249_, 2);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_base_2249_, 0);
lean_dec(v_unused_2296_);
v___x_2262_ = v_base_2249_;
v_isShared_2263_ = v_isSharedCheck_2293_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_runInBase_2260_);
lean_inc(v_m_2259_);
lean_dec(v_base_2249_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2293_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; 
lean_inc(v_a_2257_);
lean_inc_ref(v_a_2256_);
lean_inc(v_a_2255_);
lean_inc_ref(v_a_2254_);
lean_inc(v_a_2253_);
lean_inc_ref(v_a_2252_);
lean_inc_ref(v_a_2251_);
v___x_2264_ = lean_apply_8(v_m_2259_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, lean_box(0));
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_monadInfo_2265_; lean_object* v_a_2266_; lean_object* v_u_2267_; lean_object* v_v_2268_; lean_object* v_cachedPUnit_2269_; lean_object* v_cachedPUnitUnit_2270_; lean_object* v___x_2272_; 
v_monadInfo_2265_ = lean_ctor_get(v_a_2251_, 0);
v_a_2266_ = lean_ctor_get(v___x_2264_, 0);
lean_inc_n(v_a_2266_, 2);
lean_dec_ref_known(v___x_2264_, 1);
v_u_2267_ = lean_ctor_get(v_monadInfo_2265_, 1);
v_v_2268_ = lean_ctor_get(v_monadInfo_2265_, 2);
v_cachedPUnit_2269_ = lean_ctor_get(v_monadInfo_2265_, 3);
v_cachedPUnitUnit_2270_ = lean_ctor_get(v_monadInfo_2265_, 4);
lean_inc_ref(v_cachedPUnitUnit_2270_);
lean_inc_ref(v_cachedPUnit_2269_);
lean_inc(v_v_2268_);
lean_inc(v_u_2267_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 4, v_cachedPUnitUnit_2270_);
lean_ctor_set(v___x_2262_, 3, v_cachedPUnit_2269_);
lean_ctor_set(v___x_2262_, 2, v_v_2268_);
lean_ctor_set(v___x_2262_, 1, v_u_2267_);
lean_ctor_set(v___x_2262_, 0, v_a_2266_);
v___x_2272_ = v___x_2262_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2266_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_u_2267_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2268_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_cachedPUnit_2269_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_cachedPUnitUnit_2270_);
v___x_2272_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2272_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__2));
v___x_2276_ = lean_box(0);
lean_inc(v_v_2268_);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v_v_2268_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
lean_inc(v_u_2267_);
v___x_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_u_2267_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
lean_inc_ref_n(v___x_2278_, 2);
v___x_2279_ = l_Lean_mkConst(v___x_2275_, v___x_2278_);
v___x_2280_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__4));
v___x_2281_ = l_Lean_mkConst(v___x_2280_, v___x_2278_);
lean_inc_n(v_a_2266_, 2);
v___x_2282_ = l_Lean_mkAppB(v___x_2281_, v_a_2266_, v_a_2274_);
v___x_2283_ = l_Lean_mkAppB(v___x_2279_, v_a_2266_, v___x_2282_);
v___x_2284_ = l_Lean_Meta_getFVarFromUserName(v_resultName_2250_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_n(v_a_2285_, 2);
lean_dec_ref_known(v___x_2284_, 1);
lean_inc(v_a_2257_);
lean_inc_ref(v_a_2256_);
lean_inc(v_a_2255_);
lean_inc_ref(v_a_2254_);
v___x_2286_ = lean_infer_type(v_a_2285_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__7));
v___x_2289_ = l_Lean_mkConst(v___x_2288_, v___x_2278_);
v___x_2290_ = l_Lean_mkApp4(v___x_2289_, v_a_2266_, v___x_2283_, v_a_2287_, v_a_2285_);
lean_inc(v_a_2257_);
lean_inc_ref(v_a_2256_);
lean_inc(v_a_2255_);
lean_inc_ref(v_a_2254_);
lean_inc(v_a_2253_);
lean_inc_ref(v_a_2252_);
lean_inc_ref(v_a_2251_);
v___x_2291_ = lean_apply_9(v_runInBase_2260_, v___x_2290_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, lean_box(0));
return v___x_2291_;
}
else
{
lean_dec(v_a_2285_);
lean_dec_ref(v___x_2283_);
lean_dec_ref_known(v___x_2278_, 2);
lean_dec(v_a_2266_);
lean_dec_ref(v_runInBase_2260_);
return v___x_2286_;
}
}
else
{
lean_dec_ref(v___x_2283_);
lean_dec_ref_known(v___x_2278_, 2);
lean_dec(v_a_2266_);
lean_dec_ref(v_runInBase_2260_);
return v___x_2284_;
}
}
else
{
lean_dec(v_a_2266_);
lean_dec_ref(v_runInBase_2260_);
lean_dec(v_resultName_2250_);
return v___x_2273_;
}
}
}
else
{
lean_del_object(v___x_2262_);
lean_dec_ref(v_runInBase_2260_);
lean_dec(v_resultName_2250_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object* v_base_2297_, lean_object* v_resultName_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2297_, v_resultName_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(lean_object* v_info_2308_, lean_object* v_as_2309_, size_t v_i_2310_, size_t v_stop_2311_, lean_object* v_b_2312_){
_start:
{
lean_object* v___y_2314_; uint8_t v___x_2318_; 
v___x_2318_ = lean_usize_dec_eq(v_i_2310_, v_stop_2311_);
if (v___x_2318_ == 0)
{
lean_object* v_reassigns_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_reassigns_2319_ = lean_ctor_get(v_info_2308_, 1);
v___x_2320_ = lean_array_uget_borrowed(v_as_2309_, v_i_2310_);
v___x_2321_ = l_Lean_Elab_Do_MutVar_getId(v___x_2320_);
v___x_2322_ = l_Lean_NameSet_contains(v_reassigns_2319_, v___x_2321_);
lean_dec(v___x_2321_);
if (v___x_2322_ == 0)
{
v___y_2314_ = v_b_2312_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2323_; 
lean_inc(v___x_2320_);
v___x_2323_ = lean_array_push(v_b_2312_, v___x_2320_);
v___y_2314_ = v___x_2323_;
goto v___jp_2313_;
}
}
else
{
return v_b_2312_;
}
v___jp_2313_:
{
size_t v___x_2315_; size_t v___x_2316_; 
v___x_2315_ = ((size_t)1ULL);
v___x_2316_ = lean_usize_add(v_i_2310_, v___x_2315_);
v_i_2310_ = v___x_2316_;
v_b_2312_ = v___y_2314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0___boxed(lean_object* v_info_2324_, lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_stop_2327_, lean_object* v_b_2328_){
_start:
{
size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2327_);
lean_dec(v_stop_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2324_, v_as_2325_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2328_);
lean_dec_ref(v_as_2325_);
lean_dec_ref(v_info_2324_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object* v_info_2334_, lean_object* v_dec_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v_continueBase_x3f_2347_; lean_object* v_controlStack_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v_monadInfo_2376_; lean_object* v_mutVars_2377_; lean_object* v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; lean_object* v_breakBase_x3f_2382_; lean_object* v_controlStack_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; uint8_t v___y_2397_; lean_object* v_controlStack_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2409_; lean_object* v___y_2410_; uint8_t v___y_2411_; uint8_t v___y_2412_; lean_object* v_returnBase_x3f_2413_; lean_object* v_controlStack_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2427_; uint8_t v___y_2428_; uint8_t v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; uint8_t v___y_2446_; uint8_t v___y_2447_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2488_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_monadInfo_2376_ = lean_ctor_get(v_a_2336_, 0);
v_mutVars_2377_ = lean_ctor_get(v_a_2336_, 1);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_array_get_size(v_mutVars_2377_);
v___x_2529_ = ((lean_object*)(l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0));
v___x_2530_ = lean_nat_dec_lt(v___x_2527_, v___x_2528_);
if (v___x_2530_ == 0)
{
v___y_2488_ = v___x_2529_;
goto v___jp_2487_;
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((size_t)0ULL);
v___x_2532_ = lean_usize_of_nat(v___x_2528_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2334_, v_mutVars_2377_, v___x_2531_, v___x_2532_, v___x_2529_);
v___y_2488_ = v___x_2533_;
goto v___jp_2487_;
}
v___jp_2344_:
{
lean_object* v_stM_2356_; lean_object* v_resultType_2357_; lean_object* v___x_2358_; 
v_stM_2356_ = lean_ctor_get(v_controlStack_2348_, 2);
v_resultType_2357_ = lean_ctor_get(v_dec_2335_, 1);
lean_inc_ref(v_stM_2356_);
lean_inc(v___y_2355_);
lean_inc_ref(v___y_2354_);
lean_inc(v___y_2353_);
lean_inc_ref(v___y_2352_);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc_ref(v___y_2349_);
lean_inc_ref(v_resultType_2357_);
v___x_2358_ = lean_apply_9(v_stM_2356_, v_resultType_2357_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, lean_box(0));
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2367_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2363_, 0, v_dec_2335_);
lean_ctor_set(v___x_2363_, 1, v___y_2345_);
lean_ctor_set(v___x_2363_, 2, v___y_2346_);
lean_ctor_set(v___x_2363_, 3, v_continueBase_x3f_2347_);
lean_ctor_set(v___x_2363_, 4, v_controlStack_2348_);
lean_ctor_set(v___x_2363_, 5, v_a_2359_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2363_);
v___x_2365_ = v___x_2361_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v_controlStack_2348_);
lean_dec(v_continueBase_x3f_2347_);
lean_dec(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v_dec_2335_);
v_a_2368_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2358_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2358_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
v___jp_2378_:
{
if (v___y_2381_ == 0)
{
v___y_2345_ = v___y_2379_;
v___y_2346_ = v_breakBase_x3f_2382_;
v_continueBase_x3f_2347_ = v___y_2380_;
v_controlStack_2348_ = v_controlStack_2383_;
v___y_2349_ = v___y_2384_;
v___y_2350_ = v___y_2385_;
v___y_2351_ = v___y_2386_;
v___y_2352_ = v___y_2387_;
v___y_2353_ = v___y_2388_;
v___y_2354_ = v___y_2389_;
v___y_2355_ = v___y_2390_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec(v___y_2380_);
lean_inc_ref(v_controlStack_2383_);
v___x_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_controlStack_2383_);
lean_inc_ref(v_monadInfo_2376_);
v___x_2392_ = l_Lean_Elab_Do_ControlStack_continueT(v_monadInfo_2376_, v_controlStack_2383_);
v___y_2345_ = v___y_2379_;
v___y_2346_ = v_breakBase_x3f_2382_;
v_continueBase_x3f_2347_ = v___x_2391_;
v_controlStack_2348_ = v___x_2392_;
v___y_2349_ = v___y_2384_;
v___y_2350_ = v___y_2385_;
v___y_2351_ = v___y_2386_;
v___y_2352_ = v___y_2387_;
v___y_2353_ = v___y_2388_;
v___y_2354_ = v___y_2389_;
v___y_2355_ = v___y_2390_;
goto v___jp_2344_;
}
}
v___jp_2393_:
{
if (v___y_2397_ == 0)
{
lean_inc(v___y_2395_);
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___y_2396_;
v_breakBase_x3f_2382_ = v___y_2395_;
v_controlStack_2383_ = v_controlStack_2398_;
v___y_2384_ = v___y_2399_;
v___y_2385_ = v___y_2400_;
v___y_2386_ = v___y_2401_;
v___y_2387_ = v___y_2402_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
v___y_2390_ = v___y_2405_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_inc_ref(v_controlStack_2398_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v_controlStack_2398_);
lean_inc_ref(v_monadInfo_2376_);
v___x_2407_ = l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_2376_, v_controlStack_2398_);
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___y_2396_;
v_breakBase_x3f_2382_ = v___x_2406_;
v_controlStack_2383_ = v___x_2407_;
v___y_2384_ = v___y_2399_;
v___y_2385_ = v___y_2400_;
v___y_2386_ = v___y_2401_;
v___y_2387_ = v___y_2402_;
v___y_2388_ = v___y_2403_;
v___y_2389_ = v___y_2404_;
v___y_2390_ = v___y_2405_;
goto v___jp_2378_;
}
}
v___jp_2408_:
{
if (lean_obj_tag(v___y_2410_) == 1)
{
lean_object* v_val_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; lean_object* v___x_2425_; 
v_val_2422_ = lean_ctor_get(v___y_2410_, 0);
lean_inc(v_val_2422_);
lean_dec_ref_known(v___y_2410_, 1);
v_fst_2423_ = lean_ctor_get(v_val_2422_, 0);
lean_inc(v_fst_2423_);
v_snd_2424_ = lean_ctor_get(v_val_2422_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_val_2422_);
lean_inc_ref(v_monadInfo_2376_);
v___x_2425_ = l_Lean_Elab_Do_ControlStack_stateT(v_monadInfo_2376_, v_fst_2423_, v_snd_2424_, v_controlStack_2414_);
v___y_2394_ = v_returnBase_x3f_2413_;
v___y_2395_ = v___y_2409_;
v___y_2396_ = v___y_2411_;
v___y_2397_ = v___y_2412_;
v_controlStack_2398_ = v___x_2425_;
v___y_2399_ = v___y_2415_;
v___y_2400_ = v___y_2416_;
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2419_;
v___y_2404_ = v___y_2420_;
v___y_2405_ = v___y_2421_;
goto v___jp_2393_;
}
else
{
lean_dec(v___y_2410_);
v___y_2394_ = v_returnBase_x3f_2413_;
v___y_2395_ = v___y_2409_;
v___y_2396_ = v___y_2411_;
v___y_2397_ = v___y_2412_;
v_controlStack_2398_ = v_controlStack_2414_;
v___y_2399_ = v___y_2415_;
v___y_2400_ = v___y_2416_;
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2419_;
v___y_2404_ = v___y_2420_;
v___y_2405_ = v___y_2421_;
goto v___jp_2393_;
}
}
v___jp_2426_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_box(0);
lean_inc_ref(v_monadInfo_2376_);
v___x_2432_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_2376_);
if (lean_obj_tag(v___y_2427_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
v_val_2433_ = lean_ctor_get(v___y_2427_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___y_2427_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2435_ = v___y_2427_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_val_2433_);
lean_dec(v___y_2427_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
lean_inc_ref(v___x_2432_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2432_);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2432_);
v___x_2438_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; 
lean_inc_ref(v_monadInfo_2376_);
v___x_2439_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(v_monadInfo_2376_, v_val_2433_, v___x_2432_);
v___y_2409_ = v___x_2431_;
v___y_2410_ = v___y_2430_;
v___y_2411_ = v___y_2428_;
v___y_2412_ = v___y_2429_;
v_returnBase_x3f_2413_ = v___x_2438_;
v_controlStack_2414_ = v___x_2439_;
v___y_2415_ = v_a_2336_;
v___y_2416_ = v_a_2337_;
v___y_2417_ = v_a_2338_;
v___y_2418_ = v_a_2339_;
v___y_2419_ = v_a_2340_;
v___y_2420_ = v_a_2341_;
v___y_2421_ = v_a_2342_;
goto v___jp_2408_;
}
}
}
else
{
lean_dec(v___y_2427_);
v___y_2409_ = v___x_2431_;
v___y_2410_ = v___y_2430_;
v___y_2411_ = v___y_2428_;
v___y_2412_ = v___y_2429_;
v_returnBase_x3f_2413_ = v___x_2431_;
v_controlStack_2414_ = v___x_2432_;
v___y_2415_ = v_a_2336_;
v___y_2416_ = v_a_2337_;
v___y_2417_ = v_a_2338_;
v___y_2418_ = v_a_2339_;
v___y_2419_ = v_a_2340_;
v___y_2420_ = v_a_2341_;
v___y_2421_ = v_a_2342_;
goto v___jp_2408_;
}
}
v___jp_2442_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_array_get_size(v___y_2444_);
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = lean_nat_dec_eq(v___x_2448_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___y_2444_);
lean_ctor_set(v___x_2451_, 1, v___y_2445_);
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
v___y_2427_ = v___y_2443_;
v___y_2428_ = v___y_2447_;
v___y_2429_ = v___y_2446_;
v___y_2430_ = v___x_2452_;
goto v___jp_2426_;
}
else
{
lean_object* v___x_2453_; 
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2444_);
v___x_2453_ = lean_box(0);
v___y_2427_ = v___y_2443_;
v___y_2428_ = v___y_2447_;
v___y_2429_ = v___y_2446_;
v___y_2430_ = v___x_2453_;
goto v___jp_2426_;
}
}
v___jp_2454_:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2336_);
if (lean_obj_tag(v___x_2459_) == 0)
{
uint8_t v_continues_2460_; 
v_continues_2460_ = lean_ctor_get_uint8(v_info_2334_, sizeof(void*)*2 + 1);
if (v_continues_2460_ == 0)
{
lean_dec_ref_known(v___x_2459_, 1);
v___y_2443_ = v___y_2455_;
v___y_2444_ = v___y_2456_;
v___y_2445_ = v___y_2457_;
v___y_2446_ = v___y_2458_;
v___y_2447_ = v_continues_2460_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2461_; 
v_a_2461_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2459_, 1);
if (lean_obj_tag(v_a_2461_) == 0)
{
uint8_t v___x_2462_; 
v___x_2462_ = 0;
v___y_2443_ = v___y_2455_;
v___y_2444_ = v___y_2456_;
v___y_2445_ = v___y_2457_;
v___y_2446_ = v___y_2458_;
v___y_2447_ = v___x_2462_;
goto v___jp_2442_;
}
else
{
lean_dec_ref_known(v_a_2461_, 1);
v___y_2443_ = v___y_2455_;
v___y_2444_ = v___y_2456_;
v___y_2445_ = v___y_2457_;
v___y_2446_ = v___y_2458_;
v___y_2447_ = v_continues_2460_;
goto v___jp_2442_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v_dec_2335_);
v_a_2463_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2459_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2459_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
v___jp_2471_:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2336_);
if (lean_obj_tag(v___x_2475_) == 0)
{
uint8_t v_breaks_2476_; 
v_breaks_2476_ = lean_ctor_get_uint8(v_info_2334_, sizeof(void*)*2);
if (v_breaks_2476_ == 0)
{
lean_dec_ref_known(v___x_2475_, 1);
v___y_2455_ = v___y_2474_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___y_2473_;
v___y_2458_ = v_breaks_2476_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2477_; 
v_a_2477_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2475_, 1);
if (lean_obj_tag(v_a_2477_) == 0)
{
uint8_t v___x_2478_; 
v___x_2478_ = 0;
v___y_2455_ = v___y_2474_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___y_2473_;
v___y_2458_ = v___x_2478_;
goto v___jp_2454_;
}
else
{
lean_dec_ref_known(v_a_2477_, 1);
v___y_2455_ = v___y_2474_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___y_2473_;
v___y_2458_ = v_breaks_2476_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v_dec_2335_);
v_a_2479_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2475_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
v___jp_2487_:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2336_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v_resultType_2491_; size_t v_sz_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v_resultType_2491_ = lean_ctor_get(v_a_2490_, 0);
lean_inc_ref(v_resultType_2491_);
lean_dec(v_a_2490_);
v_sz_2492_ = lean_array_size(v___y_2488_);
v___x_2493_ = ((size_t)0ULL);
lean_inc_ref(v___y_2488_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_2492_, v___x_2493_, v___y_2488_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v_u_2496_; lean_object* v___x_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_u_2496_ = lean_ctor_get(v_monadInfo_2376_, 1);
lean_inc(v_u_2496_);
v___x_2497_ = l_Lean_Meta_mkProdN(v_a_2495_, v_u_2496_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
if (lean_obj_tag(v___x_2497_) == 0)
{
uint8_t v_returnsEarly_2498_; 
v_returnsEarly_2498_ = lean_ctor_get_uint8(v_info_2334_, sizeof(void*)*2 + 2);
if (v_returnsEarly_2498_ == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; 
lean_dec_ref(v_resultType_2491_);
v_a_2499_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2500_ = lean_box(0);
v___y_2472_ = v___y_2488_;
v___y_2473_ = v_a_2499_;
v___y_2474_ = v___x_2500_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_resultType_2491_);
v___y_2472_ = v___y_2488_;
v___y_2473_ = v_a_2501_;
v___y_2474_ = v___x_2502_;
goto v___jp_2471_;
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v_resultType_2491_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_dec_2335_);
v_a_2503_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2497_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2497_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec_ref(v_resultType_2491_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_dec_2335_);
v_a_2511_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2494_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2494_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_dec_2335_);
v_a_2519_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2489_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2489_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___boxed(lean_object* v_info_2534_, lean_object* v_dec_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_info_2534_, v_dec_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec_ref(v_info_2534_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object* v_l_2545_, lean_object* v_elabElem_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2547_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2547_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2559_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2547_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2605_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
if (lean_obj_tag(v_a_2556_) == 1)
{
lean_object* v_breakBase_x3f_2616_; 
v_breakBase_x3f_2616_ = lean_ctor_get(v_l_2545_, 2);
lean_inc(v_breakBase_x3f_2616_);
if (lean_obj_tag(v_breakBase_x3f_2616_) == 1)
{
lean_object* v_continueBase_x3f_2617_; lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref_known(v_a_2556_, 1);
v_continueBase_x3f_2617_ = lean_ctor_get(v_l_2545_, 3);
v_val_2618_ = lean_ctor_get(v_breakBase_x3f_2616_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_breakBase_x3f_2616_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2620_ = v_breakBase_x3f_2616_;
v_isShared_2621_ = v_isSharedCheck_2631_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_dec(v_breakBase_x3f_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2631_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
uint8_t v___y_2623_; 
if (lean_obj_tag(v_continueBase_x3f_2617_) == 0)
{
uint8_t v___x_2629_; 
v___x_2629_ = 0;
v___y_2623_ = v___x_2629_;
goto v___jp_2622_;
}
else
{
uint8_t v___x_2630_; 
v___x_2630_ = 1;
v___y_2623_ = v___x_2630_;
goto v___jp_2622_;
}
v___jp_2622_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = lean_box(v___y_2623_);
v___x_2625_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkBreak___boxed), 10, 2);
lean_closure_set(v___x_2625_, 0, v_val_2618_);
lean_closure_set(v___x_2625_, 1, v___x_2624_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2625_);
v___x_2627_ = v___x_2620_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
v___y_2605_ = v___x_2627_;
goto v___jp_2604_;
}
}
}
}
else
{
lean_dec(v_breakBase_x3f_2616_);
v___y_2605_ = v_a_2556_;
goto v___jp_2604_;
}
}
else
{
v___y_2605_ = v_a_2556_;
goto v___jp_2604_;
}
v___jp_2561_:
{
lean_object* v_origCont_2565_; lean_object* v_liftedStack_2566_; lean_object* v_liftedDoBlockResultType_2567_; lean_object* v_resultName_2568_; lean_object* v_resultType_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2587_; 
v_origCont_2565_ = lean_ctor_get(v_l_2545_, 0);
lean_inc_ref(v_origCont_2565_);
v_liftedStack_2566_ = lean_ctor_get(v_l_2545_, 4);
lean_inc_ref(v_liftedStack_2566_);
v_liftedDoBlockResultType_2567_ = lean_ctor_get(v_l_2545_, 5);
lean_inc_ref(v_liftedDoBlockResultType_2567_);
lean_dec_ref(v_l_2545_);
v_resultName_2568_ = lean_ctor_get(v_origCont_2565_, 0);
v_resultType_2569_ = lean_ctor_get(v_origCont_2565_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_origCont_2565_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_origCont_2565_, 2);
lean_dec(v_unused_2588_);
v___x_2571_ = v_origCont_2565_;
v_isShared_2572_ = v_isSharedCheck_2587_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_resultType_2569_);
lean_inc(v_resultName_2568_);
lean_dec(v_origCont_2565_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2587_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_monadInfo_2573_; lean_object* v_mutVars_2574_; lean_object* v_mutVarDefs_2575_; uint8_t v_deadCode_2576_; lean_object* v_ops_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2583_; 
v_monadInfo_2573_ = lean_ctor_get(v_a_2547_, 0);
v_mutVars_2574_ = lean_ctor_get(v_a_2547_, 1);
v_mutVarDefs_2575_ = lean_ctor_get(v_a_2547_, 2);
v_deadCode_2576_ = lean_ctor_get_uint8(v_a_2547_, sizeof(void*)*6);
v_ops_2577_ = lean_ctor_get(v_a_2547_, 5);
lean_inc(v_resultName_2568_);
v___x_2578_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkPure___boxed), 10, 2);
lean_closure_set(v___x_2578_, 0, v_liftedStack_2566_);
lean_closure_set(v___x_2578_, 1, v_resultName_2568_);
v___x_2579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2579_, 0, v___y_2564_);
lean_ctor_set(v___x_2579_, 1, v___y_2562_);
lean_ctor_set(v___x_2579_, 2, v___y_2563_);
v___x_2580_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_2579_);
lean_dec_ref_known(v___x_2579_, 3);
v___x_2581_ = 1;
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 2, v___x_2578_);
v___x_2583_ = v___x_2571_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_resultName_2568_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_resultType_2569_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v___x_2578_);
v___x_2583_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*3, v___x_2581_);
lean_inc(v_ops_2577_);
lean_inc_ref(v_mutVarDefs_2575_);
lean_inc_ref(v_mutVars_2574_);
lean_inc_ref(v_monadInfo_2573_);
v___x_2584_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2584_, 0, v_monadInfo_2573_);
lean_ctor_set(v___x_2584_, 1, v_mutVars_2574_);
lean_ctor_set(v___x_2584_, 2, v_mutVarDefs_2575_);
lean_ctor_set(v___x_2584_, 3, v_liftedDoBlockResultType_2567_);
lean_ctor_set(v___x_2584_, 4, v___x_2580_);
lean_ctor_set(v___x_2584_, 5, v_ops_2577_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*6, v_deadCode_2576_);
lean_inc(v_a_2553_);
lean_inc_ref(v_a_2552_);
lean_inc(v_a_2551_);
lean_inc_ref(v_a_2550_);
lean_inc(v_a_2549_);
lean_inc_ref(v_a_2548_);
v___x_2585_ = lean_apply_9(v_elabElem_2546_, v___x_2583_, v___x_2584_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, lean_box(0));
return v___x_2585_;
}
}
}
v___jp_2589_:
{
lean_object* v_returnBase_x3f_2592_; 
v_returnBase_x3f_2592_ = lean_ctor_get(v_l_2545_, 1);
if (lean_obj_tag(v_returnBase_x3f_2592_) == 1)
{
lean_object* v_val_2593_; lean_object* v_resultType_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2602_; 
v_val_2593_ = lean_ctor_get(v_returnBase_x3f_2592_, 0);
v_resultType_2594_ = lean_ctor_get(v_a_2560_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_a_2560_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v_a_2560_, 1);
lean_dec(v_unused_2603_);
v___x_2596_ = v_a_2560_;
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_resultType_2594_);
lean_dec(v_a_2560_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2602_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_inc(v_val_2593_);
v___x_2598_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkReturn___boxed), 10, 1);
lean_closure_set(v___x_2598_, 0, v_val_2593_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v___x_2598_);
v___x_2600_ = v___x_2596_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_resultType_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___x_2600_;
goto v___jp_2561_;
}
}
}
else
{
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2591_;
v___y_2564_ = v_a_2560_;
goto v___jp_2561_;
}
}
v___jp_2604_:
{
if (lean_obj_tag(v_a_2558_) == 1)
{
lean_object* v_continueBase_x3f_2606_; 
v_continueBase_x3f_2606_ = lean_ctor_get(v_l_2545_, 3);
lean_inc(v_continueBase_x3f_2606_);
if (lean_obj_tag(v_continueBase_x3f_2606_) == 1)
{
lean_object* v_val_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref_known(v_a_2558_, 1);
v_val_2607_ = lean_ctor_get(v_continueBase_x3f_2606_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_continueBase_x3f_2606_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2609_ = v_continueBase_x3f_2606_;
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_val_2607_);
lean_dec(v_continueBase_x3f_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkContinue___boxed), 9, 1);
lean_closure_set(v___x_2611_, 0, v_val_2607_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
v___y_2590_ = v___y_2605_;
v___y_2591_ = v___x_2613_;
goto v___jp_2589_;
}
}
}
else
{
lean_dec(v_continueBase_x3f_2606_);
v___y_2590_ = v___y_2605_;
v___y_2591_ = v_a_2558_;
goto v___jp_2589_;
}
}
else
{
v___y_2590_ = v___y_2605_;
v___y_2591_ = v_a_2558_;
goto v___jp_2589_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_a_2558_);
lean_dec(v_a_2556_);
lean_dec_ref(v_elabElem_2546_);
lean_dec_ref(v_l_2545_);
v_a_2632_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2559_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2559_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_a_2556_);
lean_dec_ref(v_elabElem_2546_);
lean_dec_ref(v_l_2545_);
v_a_2640_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2557_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2557_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref(v_elabElem_2546_);
lean_dec_ref(v_l_2545_);
v_a_2648_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2555_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2555_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift___boxed(lean_object* v_l_2656_, lean_object* v_elabElem_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Elab_Do_EffectForwarder_lift(v_l_2656_, v_elabElem_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object* v_l_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_liftedStack_2676_; lean_object* v_origCont_2677_; lean_object* v_restoreCont_2678_; lean_object* v___x_2679_; 
v_liftedStack_2676_ = lean_ctor_get(v_l_2667_, 4);
lean_inc_ref(v_liftedStack_2676_);
v_origCont_2677_ = lean_ctor_get(v_l_2667_, 0);
lean_inc_ref(v_origCont_2677_);
lean_dec_ref(v_l_2667_);
v_restoreCont_2678_ = lean_ctor_get(v_liftedStack_2676_, 4);
lean_inc_ref(v_restoreCont_2678_);
lean_dec_ref(v_liftedStack_2676_);
lean_inc(v_a_2674_);
lean_inc_ref(v_a_2673_);
lean_inc(v_a_2672_);
lean_inc_ref(v_a_2671_);
lean_inc(v_a_2670_);
lean_inc_ref(v_a_2669_);
lean_inc_ref(v_a_2668_);
v___x_2679_ = lean_apply_9(v_restoreCont_2678_, v_origCont_2677_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, lean_box(0));
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont___boxed(lean_object* v_l_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_l_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec_ref(v_a_2681_);
return v_res_2689_;
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
