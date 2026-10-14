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
lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v_bs_x27_554_; lean_object* v___y_556_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_v_552_ = lean_array_uget(v_bs_542_, v_i_541_);
v___x_553_ = lean_unsigned_to_nat(0u);
v_bs_x27_554_ = lean_array_uset(v_bs_542_, v_i_541_, v___x_553_);
v___x_570_ = l_Lean_Elab_Do_MutVar_getId(v_v_552_);
v___x_571_ = l_Lean_Meta_getFVarFromUserName(v___x_570_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v_ident_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v_ident_573_ = lean_ctor_get(v_v_552_, 0);
v___x_574_ = lean_box(0);
v___x_575_ = lean_box(0);
v___x_576_ = 0;
lean_inc(v_ident_573_);
v___x_577_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_573_, v_a_572_, v___x_574_, v___x_574_, v___x_575_, v___x_576_, v___x_576_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; 
lean_dec_ref_known(v___x_577_, 1);
v___x_578_ = l_Lean_Elab_Do_MutVar_stateValue(v_v_552_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v_v_552_);
v___y_556_ = v___x_578_;
goto v___jp_555_;
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_bs_x27_554_);
lean_dec(v_v_552_);
v_a_579_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_577_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_dec(v_v_552_);
v___y_556_ = v___x_571_;
goto v___jp_555_;
}
v___jp_555_:
{
if (lean_obj_tag(v___y_556_) == 0)
{
lean_object* v_a_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v_a_557_ = lean_ctor_get(v___y_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___y_556_, 1);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_541_, v___x_558_);
v___x_560_ = lean_array_uset(v_bs_x27_554_, v_i_541_, v_a_557_);
v_i_541_ = v___x_559_;
v_bs_542_ = v___x_560_;
goto _start;
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_bs_x27_554_);
v_a_562_ = lean_ctor_get(v___y_556_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___y_556_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___y_556_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___y_556_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object* v_sz_587_, lean_object* v_i_588_, lean_object* v_bs_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
size_t v_sz_boxed_597_; size_t v_i_boxed_598_; lean_object* v_res_599_; 
v_sz_boxed_597_ = lean_unbox_usize(v_sz_587_);
lean_dec(v_sz_587_);
v_i_boxed_598_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_597_, v_i_boxed_598_, v_bs_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object* v_muts_609_, lean_object* v_baseMonadInfo_610_, lean_object* v_base_611_, lean_object* v_00_u03c3_612_, lean_object* v_e_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
size_t v_sz_622_; size_t v___x_623_; lean_object* v___x_624_; 
v_sz_622_ = lean_array_size(v_muts_609_);
v___x_623_ = ((size_t)0ULL);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_622_, v___x_623_, v_muts_609_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_u_626_; lean_object* v___x_627_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_u_626_ = lean_ctor_get(v_baseMonadInfo_610_, 1);
lean_inc(v_u_626_);
lean_dec_ref(v_baseMonadInfo_610_);
v___x_627_ = l_Lean_Meta_mkProdMkN(v_a_625_, v_u_626_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v_fst_629_; lean_object* v_snd_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_676_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v_fst_629_ = lean_ctor_get(v_a_628_, 0);
v_snd_630_ = lean_ctor_get(v_a_628_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_676_ == 0)
{
v___x_632_ = v_a_628_;
v_isShared_633_ = v_isSharedCheck_676_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_snd_630_);
lean_inc(v_fst_629_);
lean_dec(v_a_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_676_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___x_645_; 
lean_inc_ref(v_00_u03c3_612_);
lean_inc(v_snd_630_);
v___x_645_ = l_Lean_Meta_isExprDefEq(v_snd_630_, v_00_u03c3_612_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; uint8_t v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = lean_unbox(v_a_646_);
lean_dec(v_a_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v_fst_629_);
lean_dec_ref(v_e_613_);
lean_dec_ref(v_base_611_);
v___x_648_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1);
v___x_649_ = l_Lean_MessageData_ofExpr(v_00_u03c3_612_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 7);
lean_ctor_set(v___x_632_, 1, v___x_649_);
lean_ctor_set(v___x_632_, 0, v___x_648_);
v___x_651_ = v___x_632_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_667_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v___x_652_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_MessageData_ofExpr(v_snd_630_);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_657_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_del_object(v___x_632_);
lean_dec(v_snd_630_);
lean_dec_ref(v_00_u03c3_612_);
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
v___y_637_ = v___y_616_;
v___y_638_ = v___y_617_;
v___y_639_ = v___y_618_;
v___y_640_ = v___y_619_;
v___y_641_ = v___y_620_;
goto v___jp_634_;
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_del_object(v___x_632_);
lean_dec(v_snd_630_);
lean_dec(v_fst_629_);
lean_dec_ref(v_e_613_);
lean_dec_ref(v_00_u03c3_612_);
lean_dec_ref(v_base_611_);
v_a_668_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_645_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_645_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
v___jp_634_:
{
lean_object* v_runInBase_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_runInBase_642_ = lean_ctor_get(v_base_611_, 3);
lean_inc_ref(v_runInBase_642_);
lean_dec_ref(v_base_611_);
v___x_643_ = l_Lean_Expr_app___override(v_e_613_, v_fst_629_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc_ref(v___y_635_);
v___x_644_ = lean_apply_9(v_runInBase_642_, v___x_643_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
return v___x_644_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_e_613_);
lean_dec_ref(v_00_u03c3_612_);
lean_dec_ref(v_base_611_);
v_a_677_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_627_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_627_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v_e_613_);
lean_dec_ref(v_00_u03c3_612_);
lean_dec_ref(v_base_611_);
lean_dec_ref(v_baseMonadInfo_610_);
v_a_685_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_624_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_624_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object* v_muts_693_, lean_object* v_baseMonadInfo_694_, lean_object* v_base_695_, lean_object* v_00_u03c3_696_, lean_object* v_e_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_muts_693_, v_baseMonadInfo_694_, v_base_695_, v_00_u03c3_696_, v_e_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object* v_baseMonadInfo_710_, lean_object* v_muts_711_, lean_object* v_base_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
lean_inc_ref(v_baseMonadInfo_710_);
v___x_721_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_710_, v_muts_711_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_m_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v_m_723_ = lean_ctor_get(v_base_712_, 1);
lean_inc_ref(v_m_723_);
lean_dec_ref(v_base_712_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc_ref(v___y_713_);
v___x_724_ = lean_apply_8(v_m_723_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_740_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_740_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_740_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_740_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_u_729_; lean_object* v_v_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v_u_729_ = lean_ctor_get(v_baseMonadInfo_710_, 1);
lean_inc(v_u_729_);
v_v_730_ = lean_ctor_get(v_baseMonadInfo_710_, 2);
lean_inc(v_v_730_);
lean_dec_ref(v_baseMonadInfo_710_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1));
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v_v_730_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_u_729_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_mkConst(v___x_731_, v___x_734_);
v___x_736_ = l_Lean_mkAppB(v___x_735_, v_a_722_, v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_736_);
v___x_738_ = v___x_727_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_dec(v_a_722_);
lean_dec_ref(v_baseMonadInfo_710_);
return v___x_724_;
}
}
else
{
lean_dec_ref(v_base_712_);
lean_dec_ref(v_baseMonadInfo_710_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object* v_baseMonadInfo_741_, lean_object* v_muts_742_, lean_object* v_base_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_741_, v_muts_742_, v_base_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object* v_baseMonadInfo_753_, lean_object* v_muts_754_, lean_object* v_00_u03c3_755_, lean_object* v_base_756_){
_start:
{
lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
lean_inc_ref(v_00_u03c3_755_);
lean_inc_ref_n(v_base_756_, 4);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0), 3, 2);
lean_closure_set(v___f_757_, 0, v_base_756_);
lean_closure_set(v___f_757_, 1, v_00_u03c3_755_);
lean_inc_ref_n(v_muts_754_, 3);
lean_inc_ref_n(v_baseMonadInfo_753_, 3);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed), 12, 3);
lean_closure_set(v___f_758_, 0, v_base_756_);
lean_closure_set(v___f_758_, 1, v_baseMonadInfo_753_);
lean_closure_set(v___f_758_, 2, v_muts_754_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed), 12, 3);
lean_closure_set(v___f_759_, 0, v_muts_754_);
lean_closure_set(v___f_759_, 1, v_baseMonadInfo_753_);
lean_closure_set(v___f_759_, 2, v_base_756_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed), 13, 4);
lean_closure_set(v___f_760_, 0, v_muts_754_);
lean_closure_set(v___f_760_, 1, v_baseMonadInfo_753_);
lean_closure_set(v___f_760_, 2, v_base_756_);
lean_closure_set(v___f_760_, 3, v_00_u03c3_755_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed), 11, 3);
lean_closure_set(v___f_761_, 0, v_baseMonadInfo_753_);
lean_closure_set(v___f_761_, 1, v_muts_754_);
lean_closure_set(v___f_761_, 2, v_base_756_);
v___x_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_762_, 0, v___f_757_);
lean_ctor_set(v___x_762_, 1, v___f_761_);
lean_ctor_set(v___x_762_, 2, v___f_758_);
lean_ctor_set(v___x_762_, 3, v___f_760_);
lean_ctor_set(v___x_762_, 4, v___f_759_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t v_sz_763_, size_t v_i_764_, lean_object* v_bs_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_763_, v_i_764_, v_bs_765_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object* v_sz_775_, lean_object* v_i_776_, lean_object* v_bs_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
size_t v_sz_boxed_786_; size_t v_i_boxed_787_; lean_object* v_res_788_; 
v_sz_boxed_786_ = lean_unbox_usize(v_sz_775_);
lean_dec(v_sz_775_);
v_i_boxed_787_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_786_, v_i_boxed_787_, v_bs_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object* v_baseMonadInfo_792_, lean_object* v_00_u03b1_793_){
_start:
{
lean_object* v_u_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_u_794_ = lean_ctor_get(v_baseMonadInfo_792_, 1);
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_796_ = lean_box(0);
lean_inc(v_u_794_);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v_u_794_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_mkConst(v___x_795_, v___x_797_);
v___x_799_ = l_Lean_Expr_app___override(v___x_798_, v_00_u03b1_793_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object* v_baseMonadInfo_800_, lean_object* v_00_u03b1_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_800_, v_00_u03b1_801_);
lean_dec_ref(v_baseMonadInfo_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object* v_runInBase_808_, lean_object* v_e_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_818_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2));
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_mk_empty_array_with_capacity(v___x_819_);
v___x_821_ = lean_array_push(v___x_820_, v_e_809_);
v___x_822_ = l_Lean_Meta_mkAppM(v___x_818_, v___x_821_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc_ref(v___y_810_);
v___x_824_ = lean_apply_9(v_runInBase_808_, v_a_823_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, lean_box(0));
return v___x_824_;
}
else
{
lean_dec_ref(v_runInBase_808_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object* v_runInBase_825_, lean_object* v_e_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_825_, v_e_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_835_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object* v_description_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_841_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1, &l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1);
v___x_842_ = lean_box(0);
v___x_843_ = lean_apply_1(v_description_839_, v___x_842_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_841_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object* v_dec_845_, lean_object* v_r_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_k_855_; lean_object* v___x_856_; 
v_k_855_ = lean_ctor_get(v_dec_845_, 2);
lean_inc_ref(v_k_855_);
lean_dec_ref(v_dec_845_);
lean_inc(v___y_853_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_849_);
lean_inc_ref(v___y_848_);
lean_inc_ref(v___y_847_);
v___x_856_ = lean_apply_8(v_k_855_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, lean_box(0));
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_mk_empty_array_with_capacity(v___x_858_);
v___x_860_ = lean_array_push(v___x_859_, v_r_846_);
v___x_861_ = 0;
v___x_862_ = 1;
v___x_863_ = 1;
v___x_864_ = l_Lean_Meta_mkLambdaFVars(v___x_860_, v_a_857_, v___x_861_, v___x_862_, v___x_861_, v___x_862_, v___x_863_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec_ref(v___x_860_);
return v___x_864_;
}
else
{
lean_dec_ref(v_r_846_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object* v_dec_865_, lean_object* v_r_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_dec_865_, v_r_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object* v_a_876_, lean_object* v_r_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc_ref(v___y_878_);
v___x_886_ = lean_apply_8(v_a_876_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, lean_box(0));
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; uint8_t v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_mk_empty_array_with_capacity(v___x_888_);
v___x_890_ = lean_array_push(v___x_889_, v_r_877_);
v___x_891_ = 0;
v___x_892_ = 1;
v___x_893_ = 1;
v___x_894_ = l_Lean_Meta_mkLambdaFVars(v___x_890_, v_a_887_, v___x_891_, v___x_892_, v___x_891_, v___x_892_, v___x_893_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec_ref(v___x_890_);
return v___x_894_;
}
else
{
lean_dec_ref(v_r_877_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object* v_a_895_, lean_object* v_r_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_895_, v_r_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object* v_k_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v_b_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc_ref(v___y_907_);
v___x_916_ = lean_apply_9(v_k_906_, v_b_910_, v___y_907_, v___y_908_, v___y_909_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_917_, v___y_918_, v___y_919_, v___y_920_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object* v_name_928_, uint8_t v_bi_929_, lean_object* v_type_930_, lean_object* v_k_931_, uint8_t v_kind_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___f_941_; lean_object* v___x_942_; 
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc_ref(v___y_933_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_941_, 0, v_k_931_);
lean_closure_set(v___f_941_, 1, v___y_933_);
lean_closure_set(v___f_941_, 2, v___y_934_);
lean_closure_set(v___f_941_, 3, v___y_935_);
v___x_942_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_928_, v_bi_929_, v_type_930_, v___f_941_, v_kind_932_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_942_) == 0)
{
return v___x_942_;
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object* v_name_951_, lean_object* v_bi_952_, lean_object* v_type_953_, lean_object* v_k_954_, lean_object* v_kind_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v_bi_boxed_964_; uint8_t v_kind_boxed_965_; lean_object* v_res_966_; 
v_bi_boxed_964_ = lean_unbox(v_bi_952_);
v_kind_boxed_965_ = lean_unbox(v_kind_955_);
v_res_966_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_951_, v_bi_boxed_964_, v_type_953_, v_k_954_, v_kind_boxed_965_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object* v_name_967_, lean_object* v_type_968_, lean_object* v_k_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; 
v___x_978_ = 0;
v___x_979_ = 0;
v___x_980_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_967_, v___x_978_, v_type_968_, v_k_969_, v___x_979_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object* v_name_981_, lean_object* v_type_982_, lean_object* v_k_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_981_, v_type_982_, v_k_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(0);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3));
v___x_1001_ = l_Lean_mkConst(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object* v_a_1002_, lean_object* v_getCont_1003_, lean_object* v_resultName_1004_, lean_object* v_resultType_1005_, lean_object* v___f_1006_, lean_object* v_baseMonadInfo_1007_, lean_object* v_casesOnWrapper_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Meta_getFVarFromUserName(v_a_1002_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc_ref(v___y_1009_);
v___x_1019_ = lean_apply_8(v_getCont_1003_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, lean_box(0));
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___f_1021_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1021_, 0, v_a_1020_);
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1023_ = l_Lean_Core_mkFreshUserName(v___x_1022_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4, &l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4);
v___x_1027_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1024_, v___x_1026_, v___f_1021_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
lean_inc_ref(v_resultType_1005_);
v___x_1029_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1004_, v_resultType_1005_, v___f_1006_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v_doBlockResultType_1031_; lean_object* v___x_1032_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v_doBlockResultType_1031_ = lean_ctor_get(v___y_1009_, 3);
lean_inc_ref(v_doBlockResultType_1031_);
v___x_1032_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1031_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1046_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_u_1037_; lean_object* v_v_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_u_1037_ = lean_ctor_get(v_baseMonadInfo_1007_, 1);
v_v_1038_ = lean_ctor_get(v_baseMonadInfo_1007_, 2);
lean_inc(v_v_1038_);
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_v_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1025_);
lean_inc(v_u_1037_);
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_u_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_mkConst(v_casesOnWrapper_1008_, v___x_1040_);
v___x_1042_ = l_Lean_mkApp5(v___x_1041_, v_resultType_1005_, v_a_1033_, v_a_1018_, v_a_1028_, v_a_1030_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1042_);
v___x_1044_ = v___x_1035_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_dec(v_a_1030_);
lean_dec(v_a_1028_);
lean_dec(v_a_1018_);
lean_dec(v_casesOnWrapper_1008_);
lean_dec_ref(v_resultType_1005_);
return v___x_1032_;
}
}
else
{
lean_dec(v_a_1028_);
lean_dec(v_a_1018_);
lean_dec(v_casesOnWrapper_1008_);
lean_dec_ref(v_resultType_1005_);
return v___x_1029_;
}
}
else
{
lean_dec(v_a_1018_);
lean_dec(v_casesOnWrapper_1008_);
lean_dec_ref(v___f_1006_);
lean_dec_ref(v_resultType_1005_);
lean_dec(v_resultName_1004_);
return v___x_1027_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v___f_1021_);
lean_dec(v_a_1018_);
lean_dec(v_casesOnWrapper_1008_);
lean_dec_ref(v___f_1006_);
lean_dec_ref(v_resultType_1005_);
lean_dec(v_resultName_1004_);
v_a_1047_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1023_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1023_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1018_);
lean_dec(v_casesOnWrapper_1008_);
lean_dec_ref(v___f_1006_);
lean_dec_ref(v_resultType_1005_);
lean_dec(v_resultName_1004_);
v_a_1055_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1019_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1019_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_dec(v_casesOnWrapper_1008_);
lean_dec_ref(v___f_1006_);
lean_dec_ref(v_resultType_1005_);
lean_dec(v_resultName_1004_);
lean_dec_ref(v_getCont_1003_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object* v_a_1063_, lean_object* v_getCont_1064_, lean_object* v_resultName_1065_, lean_object* v_resultType_1066_, lean_object* v___f_1067_, lean_object* v_baseMonadInfo_1068_, lean_object* v_casesOnWrapper_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1063_, v_getCont_1064_, v_resultName_1065_, v_resultType_1066_, v___f_1067_, v_baseMonadInfo_1068_, v_casesOnWrapper_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec_ref(v_baseMonadInfo_1068_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object* v_getCont_1082_, lean_object* v_baseMonadInfo_1083_, lean_object* v_casesOnWrapper_1084_, lean_object* v_restoreCont_1085_, lean_object* v_dec_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_inc_ref(v_dec_1086_);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1095_, 0, v_dec_1086_);
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1097_ = l_Lean_Core_mkFreshUserName(v___x_1096_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v_resultName_1099_; lean_object* v_resultType_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1111_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v_resultName_1099_ = lean_ctor_get(v_dec_1086_, 0);
v_resultType_1100_ = lean_ctor_get(v_dec_1086_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_dec_1086_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v_dec_1086_, 2);
lean_dec(v_unused_1112_);
v___x_1102_ = v_dec_1086_;
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_resultType_1100_);
lean_inc(v_resultName_1099_);
lean_dec(v_dec_1086_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1108_; 
lean_inc_ref(v_baseMonadInfo_1083_);
lean_inc_ref(v_resultType_1100_);
lean_inc(v_a_1098_);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed), 15, 7);
lean_closure_set(v___f_1104_, 0, v_a_1098_);
lean_closure_set(v___f_1104_, 1, v_getCont_1082_);
lean_closure_set(v___f_1104_, 2, v_resultName_1099_);
lean_closure_set(v___f_1104_, 3, v_resultType_1100_);
lean_closure_set(v___f_1104_, 4, v___f_1095_);
lean_closure_set(v___f_1104_, 5, v_baseMonadInfo_1083_);
lean_closure_set(v___f_1104_, 6, v_casesOnWrapper_1084_);
v___x_1105_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1083_, v_resultType_1100_);
lean_dec_ref(v_baseMonadInfo_1083_);
v___x_1106_ = 0;
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 2, v___f_1104_);
lean_ctor_set(v___x_1102_, 1, v___x_1105_);
lean_ctor_set(v___x_1102_, 0, v_a_1098_);
v___x_1108_ = v___x_1102_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1098_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v___f_1104_);
v___x_1108_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*3, v___x_1106_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc_ref(v___y_1087_);
v___x_1109_ = lean_apply_9(v_restoreCont_1085_, v___x_1108_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, lean_box(0));
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v___f_1095_);
lean_dec_ref(v_dec_1086_);
lean_dec_ref(v_restoreCont_1085_);
lean_dec(v_casesOnWrapper_1084_);
lean_dec_ref(v_baseMonadInfo_1083_);
lean_dec_ref(v_getCont_1082_);
v_a_1113_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1097_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1097_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object* v_getCont_1121_, lean_object* v_baseMonadInfo_1122_, lean_object* v_casesOnWrapper_1123_, lean_object* v_restoreCont_1124_, lean_object* v_dec_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1121_, v_baseMonadInfo_1122_, v_casesOnWrapper_1123_, v_restoreCont_1124_, v_dec_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object* v_baseMonadInfo_1135_, lean_object* v_stM_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1135_, v___y_1137_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc_ref(v___y_1138_);
v___x_1147_ = lean_apply_9(v_stM_1136_, v___x_1146_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object* v_baseMonadInfo_1148_, lean_object* v_stM_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1148_, v_stM_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec_ref(v_baseMonadInfo_1148_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object* v_m_1160_, lean_object* v_baseMonadInfo_1161_, lean_object* v_optionTWrapper_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; 
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1171_ = lean_apply_8(v_m_1160_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, lean_box(0));
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1186_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1186_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1186_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_u_1176_; lean_object* v_v_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v_u_1176_ = lean_ctor_get(v_baseMonadInfo_1161_, 1);
v_v_1177_ = lean_ctor_get(v_baseMonadInfo_1161_, 2);
v___x_1178_ = lean_box(0);
lean_inc(v_v_1177_);
v___x_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_v_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
lean_inc(v_u_1176_);
v___x_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_u_1176_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_mkConst(v_optionTWrapper_1162_, v___x_1180_);
v___x_1182_ = l_Lean_Expr_app___override(v___x_1181_, v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1182_);
v___x_1184_ = v___x_1174_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_dec(v_optionTWrapper_1162_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object* v_m_1187_, lean_object* v_baseMonadInfo_1188_, lean_object* v_optionTWrapper_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1187_, v_baseMonadInfo_1188_, v_optionTWrapper_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_baseMonadInfo_1188_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object* v_baseMonadInfo_1199_, lean_object* v_optionTWrapper_1200_, lean_object* v_casesOnWrapper_1201_, lean_object* v_getCont_1202_, lean_object* v_base_1203_){
_start:
{
lean_object* v_description_1204_; lean_object* v_m_1205_; lean_object* v_stM_1206_; lean_object* v_runInBase_1207_; lean_object* v_restoreCont_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1220_; 
v_description_1204_ = lean_ctor_get(v_base_1203_, 0);
v_m_1205_ = lean_ctor_get(v_base_1203_, 1);
v_stM_1206_ = lean_ctor_get(v_base_1203_, 2);
v_runInBase_1207_ = lean_ctor_get(v_base_1203_, 3);
v_restoreCont_1208_ = lean_ctor_get(v_base_1203_, 4);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_base_1203_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1210_ = v_base_1203_;
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_restoreCont_1208_);
lean_inc(v_runInBase_1207_);
lean_inc(v_stM_1206_);
lean_inc(v_m_1205_);
lean_inc(v_description_1204_);
lean_dec(v_base_1203_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1218_; 
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1212_, 0, v_runInBase_1207_);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1), 2, 1);
lean_closure_set(v___f_1213_, 0, v_description_1204_);
lean_inc_ref_n(v_baseMonadInfo_1199_, 2);
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed), 13, 4);
lean_closure_set(v___f_1214_, 0, v_getCont_1202_);
lean_closure_set(v___f_1214_, 1, v_baseMonadInfo_1199_);
lean_closure_set(v___f_1214_, 2, v_casesOnWrapper_1201_);
lean_closure_set(v___f_1214_, 3, v_restoreCont_1208_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed), 11, 2);
lean_closure_set(v___f_1215_, 0, v_baseMonadInfo_1199_);
lean_closure_set(v___f_1215_, 1, v_stM_1206_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed), 11, 3);
lean_closure_set(v___f_1216_, 0, v_m_1205_);
lean_closure_set(v___f_1216_, 1, v_baseMonadInfo_1199_);
lean_closure_set(v___f_1216_, 2, v_optionTWrapper_1200_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v___f_1214_);
lean_ctor_set(v___x_1210_, 3, v___f_1212_);
lean_ctor_set(v___x_1210_, 2, v___f_1215_);
lean_ctor_set(v___x_1210_, 1, v___f_1216_);
lean_ctor_set(v___x_1210_, 0, v___f_1213_);
v___x_1218_ = v___x_1210_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___f_1213_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___f_1216_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v___f_1215_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v___f_1212_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___f_1214_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object* v_00_u03b1_1221_, lean_object* v_name_1222_, uint8_t v_bi_1223_, lean_object* v_type_1224_, lean_object* v_k_1225_, uint8_t v_kind_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_1222_, v_bi_1223_, v_type_1224_, v_k_1225_, v_kind_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1236_, lean_object* v_name_1237_, lean_object* v_bi_1238_, lean_object* v_type_1239_, lean_object* v_k_1240_, lean_object* v_kind_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v_bi_boxed_1250_; uint8_t v_kind_boxed_1251_; lean_object* v_res_1252_; 
v_bi_boxed_1250_ = lean_unbox(v_bi_1238_);
v_kind_boxed_1251_ = lean_unbox(v_kind_1241_);
v_res_1252_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_1236_, v_name_1237_, v_bi_boxed_1250_, v_type_1239_, v_k_1240_, v_kind_boxed_1251_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object* v_00_u03b1_1253_, lean_object* v_name_1254_, lean_object* v_type_1255_, lean_object* v_k_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1254_, v_type_1255_, v_k_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_name_1267_, lean_object* v_type_1268_, lean_object* v_k_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(v_00_u03b1_1266_, v_name_1267_, v_type_1268_, v_k_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object* v_baseMonadInfo_1282_, lean_object* v_getCont_1283_, lean_object* v_00_u03b1_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; 
lean_inc(v_a_1291_);
lean_inc_ref(v_a_1290_);
lean_inc(v_a_1289_);
lean_inc_ref(v_a_1288_);
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
lean_inc_ref(v_a_1285_);
v___x_1293_ = lean_apply_8(v_getCont_1283_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, lean_box(0));
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1316_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1316_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1316_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_u_1298_; lean_object* v_resultType_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1314_; 
v_u_1298_ = lean_ctor_get(v_baseMonadInfo_1282_, 1);
v_resultType_1299_ = lean_ctor_get(v_a_1294_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_a_1294_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_a_1294_, 1);
lean_dec(v_unused_1315_);
v___x_1301_ = v_a_1294_;
v_isShared_1302_ = v_isSharedCheck_1314_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_resultType_1299_);
lean_dec(v_a_1294_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1314_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_box(0);
lean_inc(v_u_1298_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set_tag(v___x_1301_, 1);
lean_ctor_set(v___x_1301_, 1, v___x_1303_);
lean_ctor_set(v___x_1301_, 0, v_u_1298_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_u_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
lean_inc(v_u_1298_);
v___x_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_u_1298_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
v___x_1308_ = l_Lean_mkConst(v___x_1306_, v___x_1307_);
v___x_1309_ = l_Lean_mkAppB(v___x_1308_, v_resultType_1299_, v_00_u03b1_1284_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1309_);
v___x_1311_ = v___x_1296_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_00_u03b1_1284_);
v_a_1317_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1293_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1293_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object* v_baseMonadInfo_1325_, lean_object* v_getCont_1326_, lean_object* v_00_u03b1_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1325_, v_getCont_1326_, v_00_u03b1_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_baseMonadInfo_1325_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object* v_dec_1337_, lean_object* v_r_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_k_1347_; lean_object* v___x_1348_; 
v_k_1347_ = lean_ctor_get(v_dec_1337_, 2);
lean_inc_ref(v_k_1347_);
lean_dec_ref(v_dec_1337_);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc_ref(v___y_1339_);
v___x_1348_ = lean_apply_8(v_k_1347_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, lean_box(0));
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_n(v_a_1349_, 2);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_mk_empty_array_with_capacity(v___x_1350_);
v___x_1352_ = lean_array_push(v___x_1351_, v_r_1338_);
v___x_1353_ = 0;
v___x_1354_ = 1;
v___x_1355_ = 1;
v___x_1356_ = l_Lean_Meta_mkLambdaFVars(v___x_1352_, v_a_1349_, v___x_1353_, v___x_1354_, v___x_1353_, v___x_1354_, v___x_1355_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___x_1352_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
v___x_1358_ = lean_infer_type(v_a_1349_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1367_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_a_1357_);
lean_ctor_set(v___x_1363_, 1, v_a_1359_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_a_1357_);
v_a_1368_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1358_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1358_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_a_1349_);
v_a_1376_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1356_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1356_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_r_1338_);
v_a_1384_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1348_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1348_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object* v_dec_1392_, lean_object* v_r_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_dec_1392_, v_r_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object* v_a_1403_, lean_object* v_r_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_k_1413_; lean_object* v___x_1414_; 
v_k_1413_ = lean_ctor_get(v_a_1403_, 1);
lean_inc_ref(v_k_1413_);
lean_dec_ref(v_a_1403_);
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc_ref(v_r_1404_);
v___x_1414_ = lean_apply_9(v_k_1413_, v_r_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, lean_box(0));
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; uint8_t v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_mk_empty_array_with_capacity(v___x_1416_);
v___x_1418_ = lean_array_push(v___x_1417_, v_r_1404_);
v___x_1419_ = 0;
v___x_1420_ = 1;
v___x_1421_ = 1;
v___x_1422_ = l_Lean_Meta_mkLambdaFVars(v___x_1418_, v_a_1415_, v___x_1419_, v___x_1420_, v___x_1419_, v___x_1420_, v___x_1421_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec_ref(v___x_1418_);
return v___x_1422_;
}
else
{
lean_dec_ref(v_r_1404_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object* v_a_1423_, lean_object* v_r_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_a_1423_, v_r_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object* v_a_1434_, lean_object* v_getCont_1435_, lean_object* v_resultName_1436_, lean_object* v_resultType_1437_, lean_object* v___f_1438_, lean_object* v_baseMonadInfo_1439_, lean_object* v_casesOnWrapper_1440_, lean_object* v_00_u03b5_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Meta_getFVarFromUserName(v_a_1434_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1452_ = lean_apply_8(v_getCont_1435_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, lean_box(0));
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_n(v_a_1453_, 2);
lean_dec_ref_known(v___x_1452_, 1);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1454_, 0, v_a_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1456_ = l_Lean_Core_mkFreshUserName(v___x_1455_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v_resultType_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1498_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v_resultType_1458_ = lean_ctor_get(v_a_1453_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_a_1453_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v_a_1453_, 1);
lean_dec(v_unused_1499_);
v___x_1460_ = v_a_1453_;
v_isShared_1461_ = v_isSharedCheck_1498_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_resultType_1458_);
lean_dec(v_a_1453_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1498_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1457_, v_resultType_1458_, v___f_1454_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
lean_inc_ref(v_resultType_1437_);
v___x_1464_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1436_, v_resultType_1437_, v___f_1438_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1489_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1489_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1489_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_fst_1469_; lean_object* v_snd_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1488_; 
v_fst_1469_ = lean_ctor_get(v_a_1465_, 0);
v_snd_1470_ = lean_ctor_get(v_a_1465_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_a_1465_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1472_ = v_a_1465_;
v_isShared_1473_ = v_isSharedCheck_1488_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_snd_1470_);
lean_inc(v_fst_1469_);
lean_dec(v_a_1465_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1488_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v_u_1474_; lean_object* v_v_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v_u_1474_ = lean_ctor_get(v_baseMonadInfo_1439_, 1);
v_v_1475_ = lean_ctor_get(v_baseMonadInfo_1439_, 2);
v___x_1476_ = lean_box(0);
lean_inc(v_v_1475_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 1);
lean_ctor_set(v___x_1472_, 1, v___x_1476_);
lean_ctor_set(v___x_1472_, 0, v_v_1475_);
v___x_1478_ = v___x_1472_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
lean_inc(v_u_1474_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 1);
lean_ctor_set(v___x_1460_, 1, v___x_1478_);
lean_ctor_set(v___x_1460_, 0, v_u_1474_);
v___x_1480_ = v___x_1460_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_u_1474_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1481_ = l_Lean_mkConst(v_casesOnWrapper_1440_, v___x_1480_);
v___x_1482_ = l_Lean_mkApp6(v___x_1481_, v_00_u03b5_1441_, v_resultType_1437_, v_snd_1470_, v_a_1451_, v_a_1463_, v_fst_1469_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1482_);
v___x_1484_ = v___x_1467_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_a_1463_);
lean_del_object(v___x_1460_);
lean_dec(v_a_1451_);
lean_dec_ref(v_00_u03b5_1441_);
lean_dec(v_casesOnWrapper_1440_);
lean_dec_ref(v_resultType_1437_);
v_a_1490_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1464_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1464_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_del_object(v___x_1460_);
lean_dec(v_a_1451_);
lean_dec_ref(v_00_u03b5_1441_);
lean_dec(v_casesOnWrapper_1440_);
lean_dec_ref(v___f_1438_);
lean_dec_ref(v_resultType_1437_);
lean_dec(v_resultName_1436_);
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v___f_1454_);
lean_dec(v_a_1453_);
lean_dec(v_a_1451_);
lean_dec_ref(v_00_u03b5_1441_);
lean_dec(v_casesOnWrapper_1440_);
lean_dec_ref(v___f_1438_);
lean_dec_ref(v_resultType_1437_);
lean_dec(v_resultName_1436_);
v_a_1500_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1456_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1456_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_a_1451_);
lean_dec_ref(v_00_u03b5_1441_);
lean_dec(v_casesOnWrapper_1440_);
lean_dec_ref(v___f_1438_);
lean_dec_ref(v_resultType_1437_);
lean_dec(v_resultName_1436_);
v_a_1508_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1452_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1452_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1441_);
lean_dec(v_casesOnWrapper_1440_);
lean_dec_ref(v___f_1438_);
lean_dec_ref(v_resultType_1437_);
lean_dec(v_resultName_1436_);
lean_dec_ref(v_getCont_1435_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object* v_a_1516_, lean_object* v_getCont_1517_, lean_object* v_resultName_1518_, lean_object* v_resultType_1519_, lean_object* v___f_1520_, lean_object* v_baseMonadInfo_1521_, lean_object* v_casesOnWrapper_1522_, lean_object* v_00_u03b5_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1516_, v_getCont_1517_, v_resultName_1518_, v_resultType_1519_, v___f_1520_, v_baseMonadInfo_1521_, v_casesOnWrapper_1522_, v_00_u03b5_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec_ref(v_baseMonadInfo_1521_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object* v_getCont_1533_, lean_object* v_baseMonadInfo_1534_, lean_object* v_casesOnWrapper_1535_, lean_object* v_00_u03b5_1536_, lean_object* v_restoreCont_1537_, lean_object* v_dec_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___f_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_inc_ref(v_dec_1538_);
v___f_1547_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1547_, 0, v_dec_1538_);
v___x_1548_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1549_ = l_Lean_Core_mkFreshUserName(v___x_1548_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_resultName_1551_; lean_object* v_resultType_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1572_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v_resultName_1551_ = lean_ctor_get(v_dec_1538_, 0);
v_resultType_1552_ = lean_ctor_get(v_dec_1538_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_dec_1538_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_dec_1538_, 2);
lean_dec(v_unused_1573_);
v___x_1554_ = v_dec_1538_;
v_isShared_1555_ = v_isSharedCheck_1572_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_resultType_1552_);
lean_inc(v_resultName_1551_);
lean_dec(v_dec_1538_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1572_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___f_1556_; lean_object* v___x_1557_; 
lean_inc_ref(v_baseMonadInfo_1534_);
lean_inc_ref(v_resultType_1552_);
lean_inc_ref(v_getCont_1533_);
lean_inc(v_a_1550_);
v___f_1556_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed), 16, 8);
lean_closure_set(v___f_1556_, 0, v_a_1550_);
lean_closure_set(v___f_1556_, 1, v_getCont_1533_);
lean_closure_set(v___f_1556_, 2, v_resultName_1551_);
lean_closure_set(v___f_1556_, 3, v_resultType_1552_);
lean_closure_set(v___f_1556_, 4, v___f_1547_);
lean_closure_set(v___f_1556_, 5, v_baseMonadInfo_1534_);
lean_closure_set(v___f_1556_, 6, v_casesOnWrapper_1535_);
lean_closure_set(v___f_1556_, 7, v_00_u03b5_1536_);
v___x_1557_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1534_, v_getCont_1533_, v_resultType_1552_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec_ref(v_baseMonadInfo_1534_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; uint8_t v___x_1559_; lean_object* v___x_1561_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = 0;
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 2, v___f_1556_);
lean_ctor_set(v___x_1554_, 1, v_a_1558_);
lean_ctor_set(v___x_1554_, 0, v_a_1550_);
v___x_1561_ = v___x_1554_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1550_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_a_1558_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v___f_1556_);
v___x_1561_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; 
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*3, v___x_1559_);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc_ref(v___y_1539_);
v___x_1562_ = lean_apply_9(v_restoreCont_1537_, v___x_1561_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
return v___x_1562_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v___f_1556_);
lean_del_object(v___x_1554_);
lean_dec(v_a_1550_);
lean_dec_ref(v_restoreCont_1537_);
v_a_1564_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1557_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1557_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___f_1547_);
lean_dec_ref(v_dec_1538_);
lean_dec_ref(v_restoreCont_1537_);
lean_dec_ref(v_00_u03b5_1536_);
lean_dec(v_casesOnWrapper_1535_);
lean_dec_ref(v_baseMonadInfo_1534_);
lean_dec_ref(v_getCont_1533_);
v_a_1574_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1549_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1549_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object* v_getCont_1582_, lean_object* v_baseMonadInfo_1583_, lean_object* v_casesOnWrapper_1584_, lean_object* v_00_u03b5_1585_, lean_object* v_restoreCont_1586_, lean_object* v_dec_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_getCont_1582_, v_baseMonadInfo_1583_, v_casesOnWrapper_1584_, v_00_u03b5_1585_, v_restoreCont_1586_, v_dec_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1596_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0));
v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object* v_00_u03b5_1603_, lean_object* v_description_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1606_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1);
v___x_1607_ = l_Lean_MessageData_ofExpr(v_00_u03b5_1603_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_apply_1(v_description_1604_, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1610_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object* v_baseMonadInfo_1614_, lean_object* v_getCont_1615_, lean_object* v_stM_1616_, lean_object* v_00_u03b1_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1614_, v_getCont_1615_, v_00_u03b1_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
lean_inc_ref(v___y_1618_);
v___x_1628_ = lean_apply_9(v_stM_1616_, v_a_1627_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, lean_box(0));
return v___x_1628_;
}
else
{
lean_dec_ref(v_stM_1616_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object* v_baseMonadInfo_1629_, lean_object* v_getCont_1630_, lean_object* v_stM_1631_, lean_object* v_00_u03b1_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1629_, v_getCont_1630_, v_stM_1631_, v_00_u03b1_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v_baseMonadInfo_1629_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object* v_runInBase_1646_, lean_object* v_e_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1656_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1));
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_mk_empty_array_with_capacity(v___x_1657_);
v___x_1659_ = lean_array_push(v___x_1658_, v_e_1647_);
v___x_1660_ = l_Lean_Meta_mkAppM(v___x_1656_, v___x_1659_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc_ref(v___y_1648_);
v___x_1662_ = lean_apply_9(v_runInBase_1646_, v_a_1661_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, lean_box(0));
return v___x_1662_;
}
else
{
lean_dec_ref(v_runInBase_1646_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object* v_runInBase_1663_, lean_object* v_e_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1663_, v_e_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object* v_m_1674_, lean_object* v_baseMonadInfo_1675_, lean_object* v_exceptTWrapper_1676_, lean_object* v_00_u03b5_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc_ref(v___y_1678_);
v___x_1686_ = lean_apply_8(v_m_1674_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, lean_box(0));
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1701_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1701_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1701_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_u_1691_; lean_object* v_v_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v_u_1691_ = lean_ctor_get(v_baseMonadInfo_1675_, 1);
v_v_1692_ = lean_ctor_get(v_baseMonadInfo_1675_, 2);
v___x_1693_ = lean_box(0);
lean_inc(v_v_1692_);
v___x_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_v_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
lean_inc(v_u_1691_);
v___x_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_u_1691_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_mkConst(v_exceptTWrapper_1676_, v___x_1695_);
v___x_1697_ = l_Lean_mkAppB(v___x_1696_, v_00_u03b5_1677_, v_a_1687_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1697_);
v___x_1699_ = v___x_1689_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1677_);
lean_dec(v_exceptTWrapper_1676_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object* v_m_1702_, lean_object* v_baseMonadInfo_1703_, lean_object* v_exceptTWrapper_1704_, lean_object* v_00_u03b5_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1702_, v_baseMonadInfo_1703_, v_exceptTWrapper_1704_, v_00_u03b5_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_baseMonadInfo_1703_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object* v_baseMonadInfo_1715_, lean_object* v_exceptTWrapper_1716_, lean_object* v_casesOnWrapper_1717_, lean_object* v_getCont_1718_, lean_object* v_00_u03b5_1719_, lean_object* v_base_1720_){
_start:
{
lean_object* v_description_1721_; lean_object* v_m_1722_; lean_object* v_stM_1723_; lean_object* v_runInBase_1724_; lean_object* v_restoreCont_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1737_; 
v_description_1721_ = lean_ctor_get(v_base_1720_, 0);
v_m_1722_ = lean_ctor_get(v_base_1720_, 1);
v_stM_1723_ = lean_ctor_get(v_base_1720_, 2);
v_runInBase_1724_ = lean_ctor_get(v_base_1720_, 3);
v_restoreCont_1725_ = lean_ctor_get(v_base_1720_, 4);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_base_1720_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1727_ = v_base_1720_;
v_isShared_1728_ = v_isSharedCheck_1737_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_restoreCont_1725_);
lean_inc(v_runInBase_1724_);
lean_inc(v_stM_1723_);
lean_inc(v_m_1722_);
lean_inc(v_description_1721_);
lean_dec(v_base_1720_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1737_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___f_1732_; lean_object* v___f_1733_; lean_object* v___x_1735_; 
lean_inc_ref_n(v_00_u03b5_1719_, 2);
lean_inc_ref_n(v_baseMonadInfo_1715_, 2);
lean_inc_ref(v_getCont_1718_);
v___f_1729_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed), 14, 5);
lean_closure_set(v___f_1729_, 0, v_getCont_1718_);
lean_closure_set(v___f_1729_, 1, v_baseMonadInfo_1715_);
lean_closure_set(v___f_1729_, 2, v_casesOnWrapper_1717_);
lean_closure_set(v___f_1729_, 3, v_00_u03b5_1719_);
lean_closure_set(v___f_1729_, 4, v_restoreCont_1725_);
v___f_1730_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4), 3, 2);
lean_closure_set(v___f_1730_, 0, v_00_u03b5_1719_);
lean_closure_set(v___f_1730_, 1, v_description_1721_);
v___f_1731_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed), 12, 3);
lean_closure_set(v___f_1731_, 0, v_baseMonadInfo_1715_);
lean_closure_set(v___f_1731_, 1, v_getCont_1718_);
lean_closure_set(v___f_1731_, 2, v_stM_1723_);
v___f_1732_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed), 10, 1);
lean_closure_set(v___f_1732_, 0, v_runInBase_1724_);
v___f_1733_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed), 12, 4);
lean_closure_set(v___f_1733_, 0, v_m_1722_);
lean_closure_set(v___f_1733_, 1, v_baseMonadInfo_1715_);
lean_closure_set(v___f_1733_, 2, v_exceptTWrapper_1716_);
lean_closure_set(v___f_1733_, 3, v_00_u03b5_1719_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 4, v___f_1729_);
lean_ctor_set(v___x_1727_, 3, v___f_1732_);
lean_ctor_set(v___x_1727_, 2, v___f_1731_);
lean_ctor_set(v___x_1727_, 1, v___f_1733_);
lean_ctor_set(v___x_1727_, 0, v___f_1730_);
v___x_1735_ = v___x_1727_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___f_1730_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___f_1733_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v___f_1731_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v___f_1732_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v___f_1729_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object* v_baseMonadInfo_1747_, lean_object* v_00_u03c1_1748_, lean_object* v_m_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1));
v___x_1751_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4));
v___x_1752_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5));
v___x_1753_ = l_Lean_Elab_Do_ControlStack_exceptT(v_baseMonadInfo_1747_, v___x_1750_, v___x_1751_, v___x_1752_, v_00_u03c1_1748_, v_m_1749_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0));
v___x_1756_ = l_Lean_stringToMessageData(v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_1757_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1776_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1776_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_del_object(v___x_1768_);
v___x_1770_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1);
v___x_1771_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1770_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1771_;
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1774_; 
v_val_1772_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v_a_1766_, 1);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_val_1772_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_val_1772_);
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
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1765_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1765_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object* v_baseMonadInfo_1802_, lean_object* v_m_1803_){
_start:
{
lean_object* v_getCont_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_getCont_1804_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__0));
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__2));
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__4));
v___x_1807_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1802_, v___x_1805_, v___x_1806_, v_getCont_1804_, v_m_1803_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_1811_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1830_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1830_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1830_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
if (lean_obj_tag(v_a_1820_) == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_del_object(v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1);
v___x_1825_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1824_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1825_;
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1828_; 
v_val_1826_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v_a_1820_, 1);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_val_1826_);
v___x_1828_ = v___x_1822_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_val_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1831_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1819_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1819_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object* v_baseMonadInfo_1856_, lean_object* v_m_1857_){
_start:
{
lean_object* v_getCont_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_getCont_1858_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__0));
v___x_1859_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__2));
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__4));
v___x_1861_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1856_, v___x_1859_, v___x_1860_, v_getCont_1858_, v_m_1857_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object* v_mi_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_m_1873_; lean_object* v_u_1874_; lean_object* v_v_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_m_1873_ = lean_ctor_get(v_mi_1865_, 0);
lean_inc_ref(v_m_1873_);
v_u_1874_ = lean_ctor_get(v_mi_1865_, 1);
lean_inc(v_u_1874_);
v_v_1875_ = lean_ctor_get(v_mi_1865_, 2);
lean_inc(v_v_1875_);
lean_dec_ref(v_mi_1865_);
v___x_1876_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1));
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_v_1875_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_u_1874_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_mkConst(v___x_1876_, v___x_1879_);
v___x_1881_ = l_Lean_Expr_app___override(v___x_1880_, v_m_1873_);
v___x_1882_ = lean_box(0);
v___x_1883_ = l_Lean_Elab_Term_mkInstMVar(v___x_1881_, v___x_1882_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object* v_mi_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1892_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0));
v___x_1895_ = l_Lean_stringToMessageData(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2));
v___x_1898_ = l_Lean_stringToMessageData(v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4));
v___x_1901_ = l_Lean_stringToMessageData(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object* v_msg_1905_, lean_object* v_expected_1906_, lean_object* v_actual_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
lean_inc_ref(v_actual_1907_);
lean_inc_ref(v_expected_1906_);
v___x_1913_ = l_Lean_Meta_isExprDefEq(v_expected_1906_, v_actual_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1937_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1937_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1937_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_unbox(v_a_1914_);
lean_dec(v_a_1914_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_del_object(v___x_1916_);
v___x_1919_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
v___x_1920_ = l_Lean_stringToMessageData(v_msg_1905_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_MessageData_ofExpr(v_expected_1906_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_MessageData_ofExpr(v_actual_1907_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1931_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v_actual_1907_);
lean_dec_ref(v_expected_1906_);
lean_dec_ref(v_msg_1905_);
v___x_1933_ = lean_box(0);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1933_);
v___x_1935_ = v___x_1916_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_actual_1907_);
lean_dec_ref(v_expected_1906_);
lean_dec_ref(v_msg_1905_);
v_a_1938_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1913_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1913_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object* v_msg_1946_, lean_object* v_expected_1947_, lean_object* v_actual_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1946_, v_expected_1947_, v_actual_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object* v_msg_1955_, lean_object* v_expected_1956_, lean_object* v_actual_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1955_, v_expected_1956_, v_actual_1957_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object* v_msg_1967_, lean_object* v_expected_1968_, lean_object* v_actual_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_1967_, v_expected_1968_, v_actual_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec_ref(v_a_1970_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object* v_base_1984_, uint8_t v_hasContinue_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_m_1994_; lean_object* v_runInBase_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2053_; 
v_m_1994_ = lean_ctor_get(v_base_1984_, 1);
v_runInBase_1995_ = lean_ctor_get(v_base_1984_, 3);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_base_1984_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2054_ = lean_ctor_get(v_base_1984_, 4);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_base_1984_, 2);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_base_1984_, 0);
lean_dec(v_unused_2056_);
v___x_1997_ = v_base_1984_;
v_isShared_1998_ = v_isSharedCheck_2053_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_runInBase_1995_);
lean_inc(v_m_1994_);
lean_dec(v_base_1984_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2053_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; 
lean_inc(v_a_1992_);
lean_inc_ref(v_a_1991_);
lean_inc(v_a_1990_);
lean_inc_ref(v_a_1989_);
lean_inc(v_a_1988_);
lean_inc_ref(v_a_1987_);
lean_inc_ref(v_a_1986_);
v___x_1999_ = lean_apply_8(v_m_1994_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, lean_box(0));
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_monadInfo_2000_; lean_object* v_a_2001_; lean_object* v_doBlockResultType_2002_; lean_object* v_u_2003_; lean_object* v_v_2004_; lean_object* v_cachedPUnit_2005_; lean_object* v_cachedPUnitUnit_2006_; lean_object* v___x_2008_; 
v_monadInfo_2000_ = lean_ctor_get(v_a_1986_, 0);
v_a_2001_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_n(v_a_2001_, 2);
lean_dec_ref_known(v___x_1999_, 1);
v_doBlockResultType_2002_ = lean_ctor_get(v_a_1986_, 3);
v_u_2003_ = lean_ctor_get(v_monadInfo_2000_, 1);
v_v_2004_ = lean_ctor_get(v_monadInfo_2000_, 2);
v_cachedPUnit_2005_ = lean_ctor_get(v_monadInfo_2000_, 3);
v_cachedPUnitUnit_2006_ = lean_ctor_get(v_monadInfo_2000_, 4);
lean_inc_ref(v_cachedPUnitUnit_2006_);
lean_inc_ref(v_cachedPUnit_2005_);
lean_inc(v_v_2004_);
lean_inc(v_u_2003_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_cachedPUnitUnit_2006_);
lean_ctor_set(v___x_1997_, 3, v_cachedPUnit_2005_);
lean_ctor_set(v___x_1997_, 2, v_v_2004_);
lean_ctor_set(v___x_1997_, 1, v_u_2003_);
lean_ctor_set(v___x_1997_, 0, v_a_2001_);
v___x_2008_ = v___x_1997_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2001_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_u_2003_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_2004_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_cachedPUnit_2005_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_cachedPUnitUnit_2006_);
v___x_2008_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2008_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2012_ = 0;
v___x_2013_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2011_, v___x_2012_, v_a_1986_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___y_2016_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
if (v_hasContinue_1985_ == 0)
{
v___y_2016_ = v_a_2014_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2047_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_2048_ = lean_box(0);
lean_inc(v_u_2003_);
v___x_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_u_2003_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = l_Lean_mkConst(v___x_2047_, v___x_2049_);
v___x_2051_ = l_Lean_Expr_app___override(v___x_2050_, v_a_2014_);
v___y_2016_ = v___x_2051_;
goto v___jp_2015_;
}
v___jp_2015_:
{
lean_object* v___x_2017_; 
lean_inc_ref(v_doBlockResultType_2002_);
v___x_2017_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2002_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1));
v___x_2020_ = lean_box(0);
lean_inc(v_v_2004_);
v___x_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_v_2004_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
lean_inc(v_u_2003_);
v___x_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_u_2003_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = l_Lean_mkConst(v___x_2019_, v___x_2022_);
v___x_2024_ = l_Lean_mkApp3(v___x_2023_, v___y_2016_, v_a_2001_, v_a_2010_);
lean_inc(v_a_1992_);
lean_inc_ref(v_a_1991_);
lean_inc(v_a_1990_);
lean_inc_ref(v_a_1989_);
lean_inc(v_a_1988_);
lean_inc_ref(v_a_1987_);
lean_inc_ref(v_a_1986_);
v___x_2025_ = lean_apply_9(v_runInBase_1995_, v___x_2024_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, lean_box(0));
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_n(v_a_2026_, 2);
lean_dec_ref_known(v___x_2025_, 1);
lean_inc(v_a_1992_);
lean_inc_ref(v_a_1991_);
lean_inc(v_a_1990_);
lean_inc_ref(v_a_1989_);
v___x_2027_ = lean_infer_type(v_a_2026_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2));
v___x_2030_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2029_, v_a_2018_, v_a_2028_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___x_2030_, 0);
lean_dec(v_unused_2038_);
v___x_2032_ = v___x_2030_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v___x_2030_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v_a_2026_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2026_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_2026_);
v_a_2039_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2030_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2030_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_dec(v_a_2026_);
lean_dec(v_a_2018_);
return v___x_2027_;
}
}
else
{
lean_dec(v_a_2018_);
return v___x_2025_;
}
}
else
{
lean_dec_ref(v___y_2016_);
lean_dec(v_a_2010_);
lean_dec(v_a_2001_);
lean_dec_ref(v_runInBase_1995_);
return v___x_2017_;
}
}
}
else
{
lean_dec(v_a_2010_);
lean_dec(v_a_2001_);
lean_dec_ref(v_runInBase_1995_);
return v___x_2013_;
}
}
else
{
lean_dec(v_a_2001_);
lean_dec_ref(v_runInBase_1995_);
return v___x_2009_;
}
}
}
else
{
lean_del_object(v___x_1997_);
lean_dec_ref(v_runInBase_1995_);
return v___x_1999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object* v_base_2057_, lean_object* v_hasContinue_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
uint8_t v_hasContinue_boxed_2067_; lean_object* v_res_2068_; 
v_hasContinue_boxed_2067_ = lean_unbox(v_hasContinue_2058_);
v_res_2068_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2057_, v_hasContinue_boxed_2067_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec_ref(v_a_2059_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object* v_base_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_m_2083_; lean_object* v_runInBase_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2135_; 
v_m_2083_ = lean_ctor_get(v_base_2074_, 1);
v_runInBase_2084_ = lean_ctor_get(v_base_2074_, 3);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_base_2074_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; lean_object* v_unused_2137_; lean_object* v_unused_2138_; 
v_unused_2136_ = lean_ctor_get(v_base_2074_, 4);
lean_dec(v_unused_2136_);
v_unused_2137_ = lean_ctor_get(v_base_2074_, 2);
lean_dec(v_unused_2137_);
v_unused_2138_ = lean_ctor_get(v_base_2074_, 0);
lean_dec(v_unused_2138_);
v___x_2086_ = v_base_2074_;
v_isShared_2087_ = v_isSharedCheck_2135_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_runInBase_2084_);
lean_inc(v_m_2083_);
lean_dec(v_base_2074_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2135_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; 
lean_inc(v_a_2081_);
lean_inc_ref(v_a_2080_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___x_2088_ = lean_apply_8(v_m_2083_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, lean_box(0));
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_monadInfo_2089_; lean_object* v_a_2090_; lean_object* v_doBlockResultType_2091_; lean_object* v_u_2092_; lean_object* v_v_2093_; lean_object* v_cachedPUnit_2094_; lean_object* v_cachedPUnitUnit_2095_; lean_object* v___x_2097_; 
v_monadInfo_2089_ = lean_ctor_get(v_a_2075_, 0);
v_a_2090_ = lean_ctor_get(v___x_2088_, 0);
lean_inc_n(v_a_2090_, 2);
lean_dec_ref_known(v___x_2088_, 1);
v_doBlockResultType_2091_ = lean_ctor_get(v_a_2075_, 3);
v_u_2092_ = lean_ctor_get(v_monadInfo_2089_, 1);
v_v_2093_ = lean_ctor_get(v_monadInfo_2089_, 2);
v_cachedPUnit_2094_ = lean_ctor_get(v_monadInfo_2089_, 3);
v_cachedPUnitUnit_2095_ = lean_ctor_get(v_monadInfo_2089_, 4);
lean_inc_ref(v_cachedPUnitUnit_2095_);
lean_inc_ref(v_cachedPUnit_2094_);
lean_inc(v_v_2093_);
lean_inc(v_u_2092_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 4, v_cachedPUnitUnit_2095_);
lean_ctor_set(v___x_2086_, 3, v_cachedPUnit_2094_);
lean_ctor_set(v___x_2086_, 2, v_v_2093_);
lean_ctor_set(v___x_2086_, 1, v_u_2092_);
lean_ctor_set(v___x_2086_, 0, v_a_2090_);
v___x_2097_ = v___x_2086_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2090_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_u_2092_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_cachedPUnit_2094_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_cachedPUnitUnit_2095_);
v___x_2097_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2097_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2101_ = 0;
v___x_2102_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2100_, v___x_2101_, v_a_2075_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
lean_inc_ref(v_doBlockResultType_2091_);
v___x_2104_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2091_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1));
v___x_2107_ = lean_box(0);
lean_inc(v_v_2093_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v_v_2093_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
lean_inc(v_u_2092_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_u_2092_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = l_Lean_mkConst(v___x_2106_, v___x_2109_);
v___x_2111_ = l_Lean_mkApp3(v___x_2110_, v_a_2103_, v_a_2090_, v_a_2099_);
lean_inc(v_a_2081_);
lean_inc_ref(v_a_2080_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___x_2112_ = lean_apply_9(v_runInBase_2084_, v___x_2111_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, lean_box(0));
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc_n(v_a_2113_, 2);
lean_dec_ref_known(v___x_2112_, 1);
lean_inc(v_a_2081_);
lean_inc_ref(v_a_2080_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
v___x_2114_ = lean_infer_type(v_a_2113_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2));
v___x_2117_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2116_, v_a_2105_, v_a_2115_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2125_);
v___x_2119_ = v___x_2117_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v___x_2117_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v_a_2113_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2113_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_a_2113_);
v_a_2126_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2117_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2117_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_dec(v_a_2113_);
lean_dec(v_a_2105_);
return v___x_2114_;
}
}
else
{
lean_dec(v_a_2105_);
return v___x_2112_;
}
}
else
{
lean_dec(v_a_2103_);
lean_dec(v_a_2099_);
lean_dec(v_a_2090_);
lean_dec_ref(v_runInBase_2084_);
return v___x_2104_;
}
}
else
{
lean_dec(v_a_2099_);
lean_dec(v_a_2090_);
lean_dec_ref(v_runInBase_2084_);
return v___x_2102_;
}
}
else
{
lean_dec(v_a_2090_);
lean_dec_ref(v_runInBase_2084_);
return v___x_2098_;
}
}
}
else
{
lean_del_object(v___x_2086_);
lean_dec_ref(v_runInBase_2084_);
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object* v_base_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object* v_base_2157_, lean_object* v_r_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_m_2167_; lean_object* v_runInBase_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2214_; 
v_m_2167_ = lean_ctor_get(v_base_2157_, 1);
v_runInBase_2168_ = lean_ctor_get(v_base_2157_, 3);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_base_2157_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; lean_object* v_unused_2216_; lean_object* v_unused_2217_; 
v_unused_2215_ = lean_ctor_get(v_base_2157_, 4);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_base_2157_, 2);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_base_2157_, 0);
lean_dec(v_unused_2217_);
v___x_2170_ = v_base_2157_;
v_isShared_2171_ = v_isSharedCheck_2214_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_runInBase_2168_);
lean_inc(v_m_2167_);
lean_dec(v_base_2157_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2214_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; 
lean_inc(v_a_2165_);
lean_inc_ref(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
lean_inc(v_a_2161_);
lean_inc_ref(v_a_2160_);
lean_inc_ref(v_a_2159_);
v___x_2172_ = lean_apply_8(v_m_2167_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, lean_box(0));
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_monadInfo_2173_; lean_object* v_a_2174_; lean_object* v_doBlockResultType_2175_; lean_object* v_u_2176_; lean_object* v_v_2177_; lean_object* v_cachedPUnit_2178_; lean_object* v_cachedPUnitUnit_2179_; lean_object* v___x_2181_; 
v_monadInfo_2173_ = lean_ctor_get(v_a_2159_, 0);
v_a_2174_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_n(v_a_2174_, 2);
lean_dec_ref_known(v___x_2172_, 1);
v_doBlockResultType_2175_ = lean_ctor_get(v_a_2159_, 3);
v_u_2176_ = lean_ctor_get(v_monadInfo_2173_, 1);
v_v_2177_ = lean_ctor_get(v_monadInfo_2173_, 2);
v_cachedPUnit_2178_ = lean_ctor_get(v_monadInfo_2173_, 3);
v_cachedPUnitUnit_2179_ = lean_ctor_get(v_monadInfo_2173_, 4);
lean_inc_ref(v_cachedPUnitUnit_2179_);
lean_inc_ref(v_cachedPUnit_2178_);
lean_inc(v_v_2177_);
lean_inc(v_u_2176_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 4, v_cachedPUnitUnit_2179_);
lean_ctor_set(v___x_2170_, 3, v_cachedPUnit_2178_);
lean_ctor_set(v___x_2170_, 2, v_v_2177_);
lean_ctor_set(v___x_2170_, 1, v_u_2176_);
lean_ctor_set(v___x_2170_, 0, v_a_2174_);
v___x_2181_ = v___x_2170_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2174_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_u_2176_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_v_2177_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v_cachedPUnit_2178_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v_cachedPUnitUnit_2179_);
v___x_2181_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2181_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
lean_inc(v_a_2165_);
lean_inc_ref(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
lean_inc_ref(v_r_2158_);
v___x_2184_ = lean_infer_type(v_r_2158_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1));
v___x_2187_ = 0;
v___x_2188_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2186_, v___x_2187_, v_a_2159_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
lean_inc_ref(v_doBlockResultType_2175_);
v___x_2190_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2175_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
v___x_2193_ = lean_box(0);
lean_inc(v_v_2177_);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_v_2177_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_inc(v_u_2176_);
v___x_2195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_u_2176_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
lean_inc_ref(v___x_2195_);
v___x_2196_ = l_Lean_mkConst(v___x_2192_, v___x_2195_);
lean_inc(v_a_2189_);
lean_inc(v_a_2185_);
v___x_2197_ = l_Lean_mkAppB(v___x_2196_, v_a_2185_, v_a_2189_);
lean_inc(v_a_2174_);
v___x_2198_ = l_Lean_Expr_app___override(v_a_2174_, v___x_2197_);
v___x_2199_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2));
v___x_2200_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2199_, v_a_2191_, v___x_2198_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref_known(v___x_2200_, 1);
v___x_2201_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4));
v___x_2202_ = l_Lean_mkConst(v___x_2201_, v___x_2195_);
v___x_2203_ = l_Lean_mkApp5(v___x_2202_, v_a_2185_, v_a_2174_, v_a_2189_, v_a_2183_, v_r_2158_);
lean_inc(v_a_2165_);
lean_inc_ref(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
lean_inc(v_a_2161_);
lean_inc_ref(v_a_2160_);
lean_inc_ref(v_a_2159_);
v___x_2204_ = lean_apply_9(v_runInBase_2168_, v___x_2203_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, lean_box(0));
return v___x_2204_;
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref_known(v___x_2195_, 2);
lean_dec(v_a_2189_);
lean_dec(v_a_2185_);
lean_dec(v_a_2183_);
lean_dec(v_a_2174_);
lean_dec_ref(v_runInBase_2168_);
lean_dec_ref(v_r_2158_);
v_a_2205_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2200_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2200_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_dec(v_a_2189_);
lean_dec(v_a_2185_);
lean_dec(v_a_2183_);
lean_dec(v_a_2174_);
lean_dec_ref(v_runInBase_2168_);
lean_dec_ref(v_r_2158_);
return v___x_2190_;
}
}
else
{
lean_dec(v_a_2185_);
lean_dec(v_a_2183_);
lean_dec(v_a_2174_);
lean_dec_ref(v_runInBase_2168_);
lean_dec_ref(v_r_2158_);
return v___x_2188_;
}
}
else
{
lean_dec(v_a_2183_);
lean_dec(v_a_2174_);
lean_dec_ref(v_runInBase_2168_);
lean_dec_ref(v_r_2158_);
return v___x_2184_;
}
}
else
{
lean_dec(v_a_2174_);
lean_dec_ref(v_runInBase_2168_);
lean_dec_ref(v_r_2158_);
return v___x_2182_;
}
}
}
else
{
lean_del_object(v___x_2170_);
lean_dec_ref(v_runInBase_2168_);
lean_dec_ref(v_r_2158_);
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object* v_base_2218_, lean_object* v_r_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2218_, v_r_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object* v_base_2243_, lean_object* v_resultName_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_m_2253_; lean_object* v_runInBase_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2287_; 
v_m_2253_ = lean_ctor_get(v_base_2243_, 1);
v_runInBase_2254_ = lean_ctor_get(v_base_2243_, 3);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_base_2243_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2288_ = lean_ctor_get(v_base_2243_, 4);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_base_2243_, 2);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_base_2243_, 0);
lean_dec(v_unused_2290_);
v___x_2256_ = v_base_2243_;
v_isShared_2257_ = v_isSharedCheck_2287_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_runInBase_2254_);
lean_inc(v_m_2253_);
lean_dec(v_base_2243_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2287_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; 
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
lean_inc_ref(v_a_2245_);
v___x_2258_ = lean_apply_8(v_m_2253_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_monadInfo_2259_; lean_object* v_a_2260_; lean_object* v_u_2261_; lean_object* v_v_2262_; lean_object* v_cachedPUnit_2263_; lean_object* v_cachedPUnitUnit_2264_; lean_object* v___x_2266_; 
v_monadInfo_2259_ = lean_ctor_get(v_a_2245_, 0);
v_a_2260_ = lean_ctor_get(v___x_2258_, 0);
lean_inc_n(v_a_2260_, 2);
lean_dec_ref_known(v___x_2258_, 1);
v_u_2261_ = lean_ctor_get(v_monadInfo_2259_, 1);
v_v_2262_ = lean_ctor_get(v_monadInfo_2259_, 2);
v_cachedPUnit_2263_ = lean_ctor_get(v_monadInfo_2259_, 3);
v_cachedPUnitUnit_2264_ = lean_ctor_get(v_monadInfo_2259_, 4);
lean_inc_ref(v_cachedPUnitUnit_2264_);
lean_inc_ref(v_cachedPUnit_2263_);
lean_inc(v_v_2262_);
lean_inc(v_u_2261_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v_cachedPUnitUnit_2264_);
lean_ctor_set(v___x_2256_, 3, v_cachedPUnit_2263_);
lean_ctor_set(v___x_2256_, 2, v_v_2262_);
lean_ctor_set(v___x_2256_, 1, v_u_2261_);
lean_ctor_set(v___x_2256_, 0, v_a_2260_);
v___x_2266_ = v___x_2256_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2260_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_u_2261_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_v_2262_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_cachedPUnit_2263_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v_cachedPUnitUnit_2264_);
v___x_2266_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2266_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__2));
v___x_2270_ = lean_box(0);
lean_inc(v_v_2262_);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_v_2262_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
lean_inc(v_u_2261_);
v___x_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2272_, 0, v_u_2261_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
lean_inc_ref_n(v___x_2272_, 2);
v___x_2273_ = l_Lean_mkConst(v___x_2269_, v___x_2272_);
v___x_2274_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__4));
v___x_2275_ = l_Lean_mkConst(v___x_2274_, v___x_2272_);
lean_inc_n(v_a_2260_, 2);
v___x_2276_ = l_Lean_mkAppB(v___x_2275_, v_a_2260_, v_a_2268_);
v___x_2277_ = l_Lean_mkAppB(v___x_2273_, v_a_2260_, v___x_2276_);
v___x_2278_ = l_Lean_Meta_getFVarFromUserName(v_resultName_2244_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_n(v_a_2279_, 2);
lean_dec_ref_known(v___x_2278_, 1);
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
v___x_2280_ = lean_infer_type(v_a_2279_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__7));
v___x_2283_ = l_Lean_mkConst(v___x_2282_, v___x_2272_);
v___x_2284_ = l_Lean_mkApp4(v___x_2283_, v_a_2260_, v___x_2277_, v_a_2281_, v_a_2279_);
lean_inc(v_a_2251_);
lean_inc_ref(v_a_2250_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
lean_inc_ref(v_a_2245_);
v___x_2285_ = lean_apply_9(v_runInBase_2254_, v___x_2284_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, lean_box(0));
return v___x_2285_;
}
else
{
lean_dec(v_a_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref_known(v___x_2272_, 2);
lean_dec(v_a_2260_);
lean_dec_ref(v_runInBase_2254_);
return v___x_2280_;
}
}
else
{
lean_dec_ref(v___x_2277_);
lean_dec_ref_known(v___x_2272_, 2);
lean_dec(v_a_2260_);
lean_dec_ref(v_runInBase_2254_);
return v___x_2278_;
}
}
else
{
lean_dec(v_a_2260_);
lean_dec_ref(v_runInBase_2254_);
lean_dec(v_resultName_2244_);
return v___x_2267_;
}
}
}
else
{
lean_del_object(v___x_2256_);
lean_dec_ref(v_runInBase_2254_);
lean_dec(v_resultName_2244_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object* v_base_2291_, lean_object* v_resultName_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2291_, v_resultName_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(lean_object* v_info_2302_, lean_object* v_as_2303_, size_t v_i_2304_, size_t v_stop_2305_, lean_object* v_b_2306_){
_start:
{
lean_object* v___y_2308_; uint8_t v___x_2312_; 
v___x_2312_ = lean_usize_dec_eq(v_i_2304_, v_stop_2305_);
if (v___x_2312_ == 0)
{
lean_object* v_reassigns_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_reassigns_2313_ = lean_ctor_get(v_info_2302_, 1);
v___x_2314_ = lean_array_uget_borrowed(v_as_2303_, v_i_2304_);
v___x_2315_ = l_Lean_Elab_Do_MutVar_getId(v___x_2314_);
v___x_2316_ = l_Lean_NameSet_contains(v_reassigns_2313_, v___x_2315_);
lean_dec(v___x_2315_);
if (v___x_2316_ == 0)
{
v___y_2308_ = v_b_2306_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2317_; 
lean_inc(v___x_2314_);
v___x_2317_ = lean_array_push(v_b_2306_, v___x_2314_);
v___y_2308_ = v___x_2317_;
goto v___jp_2307_;
}
}
else
{
return v_b_2306_;
}
v___jp_2307_:
{
size_t v___x_2309_; size_t v___x_2310_; 
v___x_2309_ = ((size_t)1ULL);
v___x_2310_ = lean_usize_add(v_i_2304_, v___x_2309_);
v_i_2304_ = v___x_2310_;
v_b_2306_ = v___y_2308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0___boxed(lean_object* v_info_2318_, lean_object* v_as_2319_, lean_object* v_i_2320_, lean_object* v_stop_2321_, lean_object* v_b_2322_){
_start:
{
size_t v_i_boxed_2323_; size_t v_stop_boxed_2324_; lean_object* v_res_2325_; 
v_i_boxed_2323_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_stop_boxed_2324_ = lean_unbox_usize(v_stop_2321_);
lean_dec(v_stop_2321_);
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2318_, v_as_2319_, v_i_boxed_2323_, v_stop_boxed_2324_, v_b_2322_);
lean_dec_ref(v_as_2319_);
lean_dec_ref(v_info_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object* v_info_2328_, lean_object* v_dec_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v_continueBase_x3f_2341_; lean_object* v_controlStack_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v_monadInfo_2370_; lean_object* v_mutVars_2371_; lean_object* v___y_2373_; lean_object* v___y_2374_; uint8_t v___y_2375_; lean_object* v_breakBase_x3f_2376_; lean_object* v_controlStack_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2388_; lean_object* v___y_2389_; uint8_t v___y_2390_; uint8_t v___y_2391_; lean_object* v_controlStack_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2403_; lean_object* v___y_2404_; uint8_t v___y_2405_; uint8_t v___y_2406_; lean_object* v_returnBase_x3f_2407_; lean_object* v_controlStack_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2421_; uint8_t v___y_2422_; uint8_t v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; uint8_t v___y_2440_; uint8_t v___y_2441_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; uint8_t v___y_2452_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2482_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v_monadInfo_2370_ = lean_ctor_get(v_a_2330_, 0);
v_mutVars_2371_ = lean_ctor_get(v_a_2330_, 1);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_array_get_size(v_mutVars_2371_);
v___x_2523_ = ((lean_object*)(l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0));
v___x_2524_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
if (v___x_2524_ == 0)
{
v___y_2482_ = v___x_2523_;
goto v___jp_2481_;
}
else
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_nat_dec_le(v___x_2522_, v___x_2522_);
if (v___x_2525_ == 0)
{
if (v___x_2524_ == 0)
{
v___y_2482_ = v___x_2523_;
goto v___jp_2481_;
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2522_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2328_, v_mutVars_2371_, v___x_2526_, v___x_2527_, v___x_2523_);
v___y_2482_ = v___x_2528_;
goto v___jp_2481_;
}
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2522_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2328_, v_mutVars_2371_, v___x_2529_, v___x_2530_, v___x_2523_);
v___y_2482_ = v___x_2531_;
goto v___jp_2481_;
}
}
v___jp_2338_:
{
lean_object* v_stM_2350_; lean_object* v_resultType_2351_; lean_object* v___x_2352_; 
v_stM_2350_ = lean_ctor_get(v_controlStack_2342_, 2);
v_resultType_2351_ = lean_ctor_get(v_dec_2329_, 1);
lean_inc_ref(v_stM_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc_ref(v___y_2343_);
lean_inc_ref(v_resultType_2351_);
v___x_2352_ = lean_apply_9(v_stM_2350_, v_resultType_2351_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, lean_box(0));
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2357_, 0, v_dec_2329_);
lean_ctor_set(v___x_2357_, 1, v___y_2339_);
lean_ctor_set(v___x_2357_, 2, v___y_2340_);
lean_ctor_set(v___x_2357_, 3, v_continueBase_x3f_2341_);
lean_ctor_set(v___x_2357_, 4, v_controlStack_2342_);
lean_ctor_set(v___x_2357_, 5, v_a_2353_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2357_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_controlStack_2342_);
lean_dec(v_continueBase_x3f_2341_);
lean_dec(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v_dec_2329_);
v_a_2362_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2352_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
v___jp_2372_:
{
if (v___y_2375_ == 0)
{
v___y_2339_ = v___y_2373_;
v___y_2340_ = v_breakBase_x3f_2376_;
v_continueBase_x3f_2341_ = v___y_2374_;
v_controlStack_2342_ = v_controlStack_2377_;
v___y_2343_ = v___y_2378_;
v___y_2344_ = v___y_2379_;
v___y_2345_ = v___y_2380_;
v___y_2346_ = v___y_2381_;
v___y_2347_ = v___y_2382_;
v___y_2348_ = v___y_2383_;
v___y_2349_ = v___y_2384_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v___y_2374_);
lean_inc_ref(v_controlStack_2377_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_controlStack_2377_);
lean_inc_ref(v_monadInfo_2370_);
v___x_2386_ = l_Lean_Elab_Do_ControlStack_continueT(v_monadInfo_2370_, v_controlStack_2377_);
v___y_2339_ = v___y_2373_;
v___y_2340_ = v_breakBase_x3f_2376_;
v_continueBase_x3f_2341_ = v___x_2385_;
v_controlStack_2342_ = v___x_2386_;
v___y_2343_ = v___y_2378_;
v___y_2344_ = v___y_2379_;
v___y_2345_ = v___y_2380_;
v___y_2346_ = v___y_2381_;
v___y_2347_ = v___y_2382_;
v___y_2348_ = v___y_2383_;
v___y_2349_ = v___y_2384_;
goto v___jp_2338_;
}
}
v___jp_2387_:
{
if (v___y_2391_ == 0)
{
lean_inc(v___y_2389_);
v___y_2373_ = v___y_2388_;
v___y_2374_ = v___y_2389_;
v___y_2375_ = v___y_2390_;
v_breakBase_x3f_2376_ = v___y_2389_;
v_controlStack_2377_ = v_controlStack_2392_;
v___y_2378_ = v___y_2393_;
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___y_2396_;
v___y_2382_ = v___y_2397_;
v___y_2383_ = v___y_2398_;
v___y_2384_ = v___y_2399_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_inc_ref(v_controlStack_2392_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_controlStack_2392_);
lean_inc_ref(v_monadInfo_2370_);
v___x_2401_ = l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_2370_, v_controlStack_2392_);
v___y_2373_ = v___y_2388_;
v___y_2374_ = v___y_2389_;
v___y_2375_ = v___y_2390_;
v_breakBase_x3f_2376_ = v___x_2400_;
v_controlStack_2377_ = v___x_2401_;
v___y_2378_ = v___y_2393_;
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___y_2396_;
v___y_2382_ = v___y_2397_;
v___y_2383_ = v___y_2398_;
v___y_2384_ = v___y_2399_;
goto v___jp_2372_;
}
}
v___jp_2402_:
{
if (lean_obj_tag(v___y_2404_) == 1)
{
lean_object* v_val_2416_; lean_object* v_fst_2417_; lean_object* v_snd_2418_; lean_object* v___x_2419_; 
v_val_2416_ = lean_ctor_get(v___y_2404_, 0);
lean_inc(v_val_2416_);
lean_dec_ref_known(v___y_2404_, 1);
v_fst_2417_ = lean_ctor_get(v_val_2416_, 0);
lean_inc(v_fst_2417_);
v_snd_2418_ = lean_ctor_get(v_val_2416_, 1);
lean_inc(v_snd_2418_);
lean_dec(v_val_2416_);
lean_inc_ref(v_monadInfo_2370_);
v___x_2419_ = l_Lean_Elab_Do_ControlStack_stateT(v_monadInfo_2370_, v_fst_2417_, v_snd_2418_, v_controlStack_2408_);
v___y_2388_ = v_returnBase_x3f_2407_;
v___y_2389_ = v___y_2403_;
v___y_2390_ = v___y_2405_;
v___y_2391_ = v___y_2406_;
v_controlStack_2392_ = v___x_2419_;
v___y_2393_ = v___y_2409_;
v___y_2394_ = v___y_2410_;
v___y_2395_ = v___y_2411_;
v___y_2396_ = v___y_2412_;
v___y_2397_ = v___y_2413_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2415_;
goto v___jp_2387_;
}
else
{
lean_dec(v___y_2404_);
v___y_2388_ = v_returnBase_x3f_2407_;
v___y_2389_ = v___y_2403_;
v___y_2390_ = v___y_2405_;
v___y_2391_ = v___y_2406_;
v_controlStack_2392_ = v_controlStack_2408_;
v___y_2393_ = v___y_2409_;
v___y_2394_ = v___y_2410_;
v___y_2395_ = v___y_2411_;
v___y_2396_ = v___y_2412_;
v___y_2397_ = v___y_2413_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2415_;
goto v___jp_2387_;
}
}
v___jp_2420_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_box(0);
lean_inc_ref(v_monadInfo_2370_);
v___x_2426_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_2370_);
if (lean_obj_tag(v___y_2421_) == 1)
{
lean_object* v_val_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_val_2427_ = lean_ctor_get(v___y_2421_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___y_2421_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v___y_2421_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_val_2427_);
lean_dec(v___y_2421_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
lean_inc_ref(v___x_2426_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2426_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2426_);
v___x_2432_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; 
lean_inc_ref(v_monadInfo_2370_);
v___x_2433_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(v_monadInfo_2370_, v_val_2427_, v___x_2426_);
v___y_2403_ = v___x_2425_;
v___y_2404_ = v___y_2424_;
v___y_2405_ = v___y_2422_;
v___y_2406_ = v___y_2423_;
v_returnBase_x3f_2407_ = v___x_2432_;
v_controlStack_2408_ = v___x_2433_;
v___y_2409_ = v_a_2330_;
v___y_2410_ = v_a_2331_;
v___y_2411_ = v_a_2332_;
v___y_2412_ = v_a_2333_;
v___y_2413_ = v_a_2334_;
v___y_2414_ = v_a_2335_;
v___y_2415_ = v_a_2336_;
goto v___jp_2402_;
}
}
}
else
{
lean_dec(v___y_2421_);
v___y_2403_ = v___x_2425_;
v___y_2404_ = v___y_2424_;
v___y_2405_ = v___y_2422_;
v___y_2406_ = v___y_2423_;
v_returnBase_x3f_2407_ = v___x_2425_;
v_controlStack_2408_ = v___x_2426_;
v___y_2409_ = v_a_2330_;
v___y_2410_ = v_a_2331_;
v___y_2411_ = v_a_2332_;
v___y_2412_ = v_a_2333_;
v___y_2413_ = v_a_2334_;
v___y_2414_ = v_a_2335_;
v___y_2415_ = v_a_2336_;
goto v___jp_2402_;
}
}
v___jp_2436_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2442_ = lean_array_get_size(v___y_2438_);
v___x_2443_ = lean_unsigned_to_nat(0u);
v___x_2444_ = lean_nat_dec_eq(v___x_2442_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___y_2438_);
lean_ctor_set(v___x_2445_, 1, v___y_2439_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
v___y_2421_ = v___y_2437_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___y_2440_;
v___y_2424_ = v___x_2446_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2447_; 
lean_dec_ref(v___y_2439_);
lean_dec_ref(v___y_2438_);
v___x_2447_ = lean_box(0);
v___y_2421_ = v___y_2437_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___y_2440_;
v___y_2424_ = v___x_2447_;
goto v___jp_2420_;
}
}
v___jp_2448_:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2330_);
if (lean_obj_tag(v___x_2453_) == 0)
{
uint8_t v_continues_2454_; 
v_continues_2454_ = lean_ctor_get_uint8(v_info_2328_, sizeof(void*)*2 + 1);
if (v_continues_2454_ == 0)
{
lean_dec_ref_known(v___x_2453_, 1);
v___y_2437_ = v___y_2449_;
v___y_2438_ = v___y_2450_;
v___y_2439_ = v___y_2451_;
v___y_2440_ = v___y_2452_;
v___y_2441_ = v_continues_2454_;
goto v___jp_2436_;
}
else
{
lean_object* v_a_2455_; 
v_a_2455_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2453_, 1);
if (lean_obj_tag(v_a_2455_) == 0)
{
uint8_t v___x_2456_; 
v___x_2456_ = 0;
v___y_2437_ = v___y_2449_;
v___y_2438_ = v___y_2450_;
v___y_2439_ = v___y_2451_;
v___y_2440_ = v___y_2452_;
v___y_2441_ = v___x_2456_;
goto v___jp_2436_;
}
else
{
lean_dec_ref_known(v_a_2455_, 1);
v___y_2437_ = v___y_2449_;
v___y_2438_ = v___y_2450_;
v___y_2439_ = v___y_2451_;
v___y_2440_ = v___y_2452_;
v___y_2441_ = v_continues_2454_;
goto v___jp_2436_;
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v_dec_2329_);
v_a_2457_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2453_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2453_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
v___jp_2465_:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2330_);
if (lean_obj_tag(v___x_2469_) == 0)
{
uint8_t v_breaks_2470_; 
v_breaks_2470_ = lean_ctor_get_uint8(v_info_2328_, sizeof(void*)*2);
if (v_breaks_2470_ == 0)
{
lean_dec_ref_known(v___x_2469_, 1);
v___y_2449_ = v___y_2468_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___y_2467_;
v___y_2452_ = v_breaks_2470_;
goto v___jp_2448_;
}
else
{
lean_object* v_a_2471_; 
v_a_2471_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2469_, 1);
if (lean_obj_tag(v_a_2471_) == 0)
{
uint8_t v___x_2472_; 
v___x_2472_ = 0;
v___y_2449_ = v___y_2468_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___y_2467_;
v___y_2452_ = v___x_2472_;
goto v___jp_2448_;
}
else
{
lean_dec_ref_known(v_a_2471_, 1);
v___y_2449_ = v___y_2468_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___y_2467_;
v___y_2452_ = v_breaks_2470_;
goto v___jp_2448_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v_dec_2329_);
v_a_2473_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2469_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2469_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
v___jp_2481_:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2330_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v_resultType_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_resultType_2485_ = lean_ctor_get(v_a_2484_, 0);
lean_inc_ref(v_resultType_2485_);
lean_dec(v_a_2484_);
v_sz_2486_ = lean_array_size(v___y_2482_);
v___x_2487_ = ((size_t)0ULL);
lean_inc_ref(v___y_2482_);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_2486_, v___x_2487_, v___y_2482_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v_u_2490_; lean_object* v___x_2491_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v_u_2490_ = lean_ctor_get(v_monadInfo_2370_, 1);
lean_inc(v_u_2490_);
v___x_2491_ = l_Lean_Meta_mkProdN(v_a_2489_, v_u_2490_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2491_) == 0)
{
uint8_t v_returnsEarly_2492_; 
v_returnsEarly_2492_ = lean_ctor_get_uint8(v_info_2328_, sizeof(void*)*2 + 2);
if (v_returnsEarly_2492_ == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
lean_dec_ref(v_resultType_2485_);
v_a_2493_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2494_ = lean_box(0);
v___y_2466_ = v___y_2482_;
v___y_2467_ = v_a_2493_;
v___y_2468_ = v___x_2494_;
goto v___jp_2465_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2495_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_resultType_2485_);
v___y_2466_ = v___y_2482_;
v___y_2467_ = v_a_2495_;
v___y_2468_ = v___x_2496_;
goto v___jp_2465_;
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec_ref(v_resultType_2485_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_dec_2329_);
v_a_2497_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2491_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2491_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v_resultType_2485_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_dec_2329_);
v_a_2505_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2488_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2488_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_dec_2329_);
v_a_2513_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2483_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2483_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___boxed(lean_object* v_info_2532_, lean_object* v_dec_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_info_2532_, v_dec_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec_ref(v_info_2532_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object* v_l_2543_, lean_object* v_elabElem_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2545_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2545_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2545_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2603_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
if (lean_obj_tag(v_a_2554_) == 1)
{
lean_object* v_breakBase_x3f_2614_; 
v_breakBase_x3f_2614_ = lean_ctor_get(v_l_2543_, 2);
lean_inc(v_breakBase_x3f_2614_);
if (lean_obj_tag(v_breakBase_x3f_2614_) == 1)
{
lean_object* v_continueBase_x3f_2615_; lean_object* v_val_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref_known(v_a_2554_, 1);
v_continueBase_x3f_2615_ = lean_ctor_get(v_l_2543_, 3);
v_val_2616_ = lean_ctor_get(v_breakBase_x3f_2614_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_breakBase_x3f_2614_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2618_ = v_breakBase_x3f_2614_;
v_isShared_2619_ = v_isSharedCheck_2629_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_val_2616_);
lean_dec(v_breakBase_x3f_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2629_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
uint8_t v___y_2621_; 
if (lean_obj_tag(v_continueBase_x3f_2615_) == 0)
{
uint8_t v___x_2627_; 
v___x_2627_ = 0;
v___y_2621_ = v___x_2627_;
goto v___jp_2620_;
}
else
{
uint8_t v___x_2628_; 
v___x_2628_ = 1;
v___y_2621_ = v___x_2628_;
goto v___jp_2620_;
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_box(v___y_2621_);
v___x_2623_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkBreak___boxed), 10, 2);
lean_closure_set(v___x_2623_, 0, v_val_2616_);
lean_closure_set(v___x_2623_, 1, v___x_2622_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2623_);
v___x_2625_ = v___x_2618_;
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
v___y_2603_ = v___x_2625_;
goto v___jp_2602_;
}
}
}
}
else
{
lean_dec(v_breakBase_x3f_2614_);
v___y_2603_ = v_a_2554_;
goto v___jp_2602_;
}
}
else
{
v___y_2603_ = v_a_2554_;
goto v___jp_2602_;
}
v___jp_2559_:
{
lean_object* v_origCont_2563_; lean_object* v_liftedStack_2564_; lean_object* v_liftedDoBlockResultType_2565_; lean_object* v_resultName_2566_; lean_object* v_resultType_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2585_; 
v_origCont_2563_ = lean_ctor_get(v_l_2543_, 0);
lean_inc_ref(v_origCont_2563_);
v_liftedStack_2564_ = lean_ctor_get(v_l_2543_, 4);
lean_inc_ref(v_liftedStack_2564_);
v_liftedDoBlockResultType_2565_ = lean_ctor_get(v_l_2543_, 5);
lean_inc_ref(v_liftedDoBlockResultType_2565_);
lean_dec_ref(v_l_2543_);
v_resultName_2566_ = lean_ctor_get(v_origCont_2563_, 0);
v_resultType_2567_ = lean_ctor_get(v_origCont_2563_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_origCont_2563_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_origCont_2563_, 2);
lean_dec(v_unused_2586_);
v___x_2569_ = v_origCont_2563_;
v_isShared_2570_ = v_isSharedCheck_2585_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_resultType_2567_);
lean_inc(v_resultName_2566_);
lean_dec(v_origCont_2563_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2585_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_monadInfo_2571_; lean_object* v_mutVars_2572_; lean_object* v_mutVarDefs_2573_; uint8_t v_deadCode_2574_; lean_object* v_ops_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2581_; 
v_monadInfo_2571_ = lean_ctor_get(v_a_2545_, 0);
v_mutVars_2572_ = lean_ctor_get(v_a_2545_, 1);
v_mutVarDefs_2573_ = lean_ctor_get(v_a_2545_, 2);
v_deadCode_2574_ = lean_ctor_get_uint8(v_a_2545_, sizeof(void*)*6);
v_ops_2575_ = lean_ctor_get(v_a_2545_, 5);
lean_inc(v_resultName_2566_);
v___x_2576_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkPure___boxed), 10, 2);
lean_closure_set(v___x_2576_, 0, v_liftedStack_2564_);
lean_closure_set(v___x_2576_, 1, v_resultName_2566_);
v___x_2577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2577_, 0, v___y_2562_);
lean_ctor_set(v___x_2577_, 1, v___y_2560_);
lean_ctor_set(v___x_2577_, 2, v___y_2561_);
v___x_2578_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_2577_);
lean_dec_ref_known(v___x_2577_, 3);
v___x_2579_ = 1;
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 2, v___x_2576_);
v___x_2581_ = v___x_2569_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_resultName_2566_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_resultType_2567_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v___x_2576_);
v___x_2581_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*3, v___x_2579_);
lean_inc(v_ops_2575_);
lean_inc_ref(v_mutVarDefs_2573_);
lean_inc_ref(v_mutVars_2572_);
lean_inc_ref(v_monadInfo_2571_);
v___x_2582_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2582_, 0, v_monadInfo_2571_);
lean_ctor_set(v___x_2582_, 1, v_mutVars_2572_);
lean_ctor_set(v___x_2582_, 2, v_mutVarDefs_2573_);
lean_ctor_set(v___x_2582_, 3, v_liftedDoBlockResultType_2565_);
lean_ctor_set(v___x_2582_, 4, v___x_2578_);
lean_ctor_set(v___x_2582_, 5, v_ops_2575_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*6, v_deadCode_2574_);
lean_inc(v_a_2551_);
lean_inc_ref(v_a_2550_);
lean_inc(v_a_2549_);
lean_inc_ref(v_a_2548_);
lean_inc(v_a_2547_);
lean_inc_ref(v_a_2546_);
v___x_2583_ = lean_apply_9(v_elabElem_2544_, v___x_2581_, v___x_2582_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, lean_box(0));
return v___x_2583_;
}
}
}
v___jp_2587_:
{
lean_object* v_returnBase_x3f_2590_; 
v_returnBase_x3f_2590_ = lean_ctor_get(v_l_2543_, 1);
if (lean_obj_tag(v_returnBase_x3f_2590_) == 1)
{
lean_object* v_val_2591_; lean_object* v_resultType_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_val_2591_ = lean_ctor_get(v_returnBase_x3f_2590_, 0);
v_resultType_2592_ = lean_ctor_get(v_a_2558_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_a_2558_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v_a_2558_, 1);
lean_dec(v_unused_2601_);
v___x_2594_ = v_a_2558_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_resultType_2592_);
lean_dec(v_a_2558_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
lean_inc(v_val_2591_);
v___x_2596_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkReturn___boxed), 10, 1);
lean_closure_set(v___x_2596_, 0, v_val_2591_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v___x_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_resultType_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
v___y_2560_ = v___y_2588_;
v___y_2561_ = v___y_2589_;
v___y_2562_ = v___x_2598_;
goto v___jp_2559_;
}
}
}
else
{
v___y_2560_ = v___y_2588_;
v___y_2561_ = v___y_2589_;
v___y_2562_ = v_a_2558_;
goto v___jp_2559_;
}
}
v___jp_2602_:
{
if (lean_obj_tag(v_a_2556_) == 1)
{
lean_object* v_continueBase_x3f_2604_; 
v_continueBase_x3f_2604_ = lean_ctor_get(v_l_2543_, 3);
lean_inc(v_continueBase_x3f_2604_);
if (lean_obj_tag(v_continueBase_x3f_2604_) == 1)
{
lean_object* v_val_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref_known(v_a_2556_, 1);
v_val_2605_ = lean_ctor_get(v_continueBase_x3f_2604_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_continueBase_x3f_2604_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2607_ = v_continueBase_x3f_2604_;
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_val_2605_);
lean_dec(v_continueBase_x3f_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2609_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkContinue___boxed), 9, 1);
lean_closure_set(v___x_2609_, 0, v_val_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
v___y_2588_ = v___y_2603_;
v___y_2589_ = v___x_2611_;
goto v___jp_2587_;
}
}
}
else
{
lean_dec(v_continueBase_x3f_2604_);
v___y_2588_ = v___y_2603_;
v___y_2589_ = v_a_2556_;
goto v___jp_2587_;
}
}
else
{
v___y_2588_ = v___y_2603_;
v___y_2589_ = v_a_2556_;
goto v___jp_2587_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2556_);
lean_dec(v_a_2554_);
lean_dec_ref(v_elabElem_2544_);
lean_dec_ref(v_l_2543_);
v_a_2630_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2557_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2557_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_a_2554_);
lean_dec_ref(v_elabElem_2544_);
lean_dec_ref(v_l_2543_);
v_a_2638_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2555_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2555_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v_elabElem_2544_);
lean_dec_ref(v_l_2543_);
v_a_2646_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2553_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2553_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift___boxed(lean_object* v_l_2654_, lean_object* v_elabElem_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Elab_Do_EffectForwarder_lift(v_l_2654_, v_elabElem_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec_ref(v_a_2656_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object* v_l_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_liftedStack_2674_; lean_object* v_origCont_2675_; lean_object* v_restoreCont_2676_; lean_object* v___x_2677_; 
v_liftedStack_2674_ = lean_ctor_get(v_l_2665_, 4);
lean_inc_ref(v_liftedStack_2674_);
v_origCont_2675_ = lean_ctor_get(v_l_2665_, 0);
lean_inc_ref(v_origCont_2675_);
lean_dec_ref(v_l_2665_);
v_restoreCont_2676_ = lean_ctor_get(v_liftedStack_2674_, 4);
lean_inc_ref(v_restoreCont_2676_);
lean_dec_ref(v_liftedStack_2674_);
lean_inc(v_a_2672_);
lean_inc_ref(v_a_2671_);
lean_inc(v_a_2670_);
lean_inc_ref(v_a_2669_);
lean_inc(v_a_2668_);
lean_inc_ref(v_a_2667_);
lean_inc_ref(v_a_2666_);
v___x_2677_ = lean_apply_9(v_restoreCont_2676_, v_origCont_2675_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, lean_box(0));
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont___boxed(lean_object* v_l_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_l_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec_ref(v_a_2679_);
return v_res_2687_;
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
