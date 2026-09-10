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
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_mkProdN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getBreakCont___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__2));
v___x_53_ = l_Lean_stringToMessageData(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__4));
v___x_56_ = l_Lean_stringToMessageData(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__6));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM(lean_object* v_m_60_, lean_object* v_stM_u03b1_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_71_ = 0;
v___x_72_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_70_, v___x_71_, v_a_62_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v_stM_74_; lean_object* v___x_75_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_n(v_a_73_, 2);
lean_dec_ref_known(v___x_72_, 1);
v_stM_74_ = lean_ctor_get(v_m_60_, 2);
lean_inc_ref(v_stM_74_);
lean_dec_ref(v_m_60_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc_ref(v_a_62_);
v___x_75_ = lean_apply_9(v_stM_74_, v_a_73_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, lean_box(0));
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_n(v_a_76_, 2);
lean_dec_ref_known(v___x_75_, 1);
lean_inc_ref(v_stM_u03b1_61_);
v___x_77_ = l_Lean_Meta_isExprDefEq(v_stM_u03b1_61_, v_a_76_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_104_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_104_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint8_t v___x_82_; 
v___x_82_ = lean_unbox(v_a_78_);
lean_dec(v_a_78_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_del_object(v___x_80_);
lean_dec(v_a_73_);
v___x_83_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__3, &l_Lean_Elab_Do_ControlStack_unStM___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3);
v___x_84_ = l_Lean_MessageData_ofExpr(v_stM_u03b1_61_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__5, &l_Lean_Elab_Do_ControlStack_unStM___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Lean_MessageData_ofExpr(v_a_76_);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__7, &l_Lean_Elab_Do_ControlStack_unStM___closed__7_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_91_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v___x_102_; 
lean_dec(v_a_76_);
lean_dec_ref(v_stM_u03b1_61_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v_a_73_);
v___x_102_ = v___x_80_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_73_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec(v_a_76_);
lean_dec(v_a_73_);
lean_dec_ref(v_stM_u03b1_61_);
v_a_105_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_77_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_77_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_dec(v_a_73_);
lean_dec_ref(v_stM_u03b1_61_);
return v___x_75_;
}
}
else
{
lean_dec_ref(v_stM_u03b1_61_);
lean_dec_ref(v_m_60_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM___boxed(lean_object* v_m_113_, lean_object* v_stM_u03b1_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Elab_Do_ControlStack_unStM(v_m_113_, v_stM_u03b1_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(lean_object* v_00_u03b1_124_, lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_125_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___boxed(lean_object* v_00_u03b1_135_, lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(v_00_u03b1_135_, v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0(lean_object* v_dec_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v_dec_146_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0___boxed(lean_object* v_dec_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_Do_ControlStack_base___lam__0(v_dec_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1(lean_object* v_00_u03b1_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v_00_u03b1_166_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1___boxed(lean_object* v_00_u03b1_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Elab_Do_ControlStack_base___lam__1(v_00_u03b1_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_185_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1));
v___x_190_ = l_Lean_MessageData_ofFormat(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2(lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2, &l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once, _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3(lean_object* v_m_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_m_193_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3___boxed(lean_object* v_m_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_Do_ControlStack_base___lam__3(v_m_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base(lean_object* v_mi_216_){
_start:
{
lean_object* v_m_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_228_; 
v_m_217_ = lean_ctor_get(v_mi_216_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_mi_216_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_229_ = lean_ctor_get(v_mi_216_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_mi_216_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_mi_216_, 2);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_mi_216_, 1);
lean_dec(v_unused_232_);
v___x_219_ = v_mi_216_;
v_isShared_220_ = v_isSharedCheck_228_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_m_217_);
lean_dec(v_mi_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_228_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_226_; 
v___f_221_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__0));
v___f_222_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__1));
v___f_223_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__2));
v___f_224_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_base___lam__3___boxed), 9, 1);
lean_closure_set(v___f_224_, 0, v_m_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 4, v___f_221_);
lean_ctor_set(v___x_219_, 3, v___f_222_);
lean_ctor_set(v___x_219_, 2, v___f_222_);
lean_ctor_set(v___x_219_, 1, v___f_224_);
lean_ctor_set(v___x_219_, 0, v___f_223_);
v___x_226_ = v___x_219_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v___f_222_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v___f_222_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v___f_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(size_t v_sz_233_, size_t v_i_234_, lean_object* v_bs_235_){
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
v___x_240_ = l_Lean_Elab_Do_MutVar_getId(v_v_237_);
lean_dec(v_v_237_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_234_, v___x_241_);
v___x_243_ = lean_array_uset(v_bs_x27_239_, v_i_234_, v___x_240_);
v_i_234_ = v___x_242_;
v_bs_235_ = v___x_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0___boxed(lean_object* v_sz_245_, lean_object* v_i_246_, lean_object* v_bs_247_){
_start:
{
size_t v_sz_boxed_248_; size_t v_i_boxed_249_; lean_object* v_res_250_; 
v_sz_boxed_248_ = lean_unbox_usize(v_sz_245_);
lean_dec(v_sz_245_);
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_res_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_boxed_248_, v_i_boxed_249_, v_bs_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(lean_object* v_muts_251_){
_start:
{
size_t v_sz_252_; size_t v___x_253_; lean_object* v___x_254_; 
v_sz_252_ = lean_array_size(v_muts_251_);
v___x_253_ = ((size_t)0ULL);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_252_, v___x_253_, v_muts_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(size_t v_sz_255_, size_t v_i_256_, lean_object* v_bs_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_usize_dec_lt(v_i_256_, v_sz_255_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v_bs_257_);
return v___x_264_;
}
else
{
lean_object* v_v_265_; lean_object* v___x_266_; 
v_v_265_ = lean_array_uget_borrowed(v_bs_257_, v_i_256_);
lean_inc(v_v_265_);
v___x_266_ = l_Lean_Meta_getLocalDeclFromUserName(v_v_265_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v_bs_x27_269_; lean_object* v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v___x_268_ = lean_unsigned_to_nat(0u);
v_bs_x27_269_ = lean_array_uset(v_bs_257_, v_i_256_, v___x_268_);
v___x_270_ = l_Lean_LocalDecl_type(v_a_267_);
lean_dec(v_a_267_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_256_, v___x_271_);
v___x_273_ = lean_array_uset(v_bs_x27_269_, v_i_256_, v___x_270_);
v_i_256_ = v___x_272_;
v_bs_257_ = v___x_273_;
goto _start;
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_bs_257_);
v_a_275_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_266_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_266_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg___boxed(lean_object* v_sz_283_, lean_object* v_i_284_, lean_object* v_bs_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
size_t v_sz_boxed_291_; size_t v_i_boxed_292_; lean_object* v_res_293_; 
v_sz_boxed_291_ = lean_unbox_usize(v_sz_283_);
lean_dec(v_sz_283_);
v_i_boxed_292_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_boxed_291_, v_i_boxed_292_, v_bs_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(lean_object* v_baseMonadInfo_294_, lean_object* v_muts_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; size_t v_sz_305_; size_t v___x_306_; lean_object* v___x_307_; 
v___x_304_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_muts_295_);
v_sz_305_ = lean_array_size(v___x_304_);
v___x_306_ = ((size_t)0ULL);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_305_, v___x_306_, v___x_304_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_u_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_u_309_ = lean_ctor_get(v_baseMonadInfo_294_, 1);
lean_inc(v_u_309_);
lean_dec_ref(v_baseMonadInfo_294_);
v___x_310_ = l_Lean_Meta_mkProdN(v_a_308_, v_u_309_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
return v___x_310_;
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v_baseMonadInfo_294_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1(lean_object* v_baseMonadInfo_416_, lean_object* v_muts_417_, lean_object* v_base_418_, lean_object* v_00_u03b1_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_416_, v_muts_417_, v_00_u03b1_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v_stM_430_; lean_object* v___x_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v_stM_430_ = lean_ctor_get(v_base_418_, 2);
lean_inc_ref(v_stM_430_);
lean_dec_ref(v_base_418_);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_431_ = lean_apply_9(v_stM_430_, v_a_429_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, lean_box(0));
return v___x_431_;
}
else
{
lean_dec_ref(v_base_418_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(lean_object* v_baseMonadInfo_432_, lean_object* v_muts_433_, lean_object* v_base_434_, lean_object* v_00_u03b1_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(v_baseMonadInfo_432_, v_muts_433_, v_base_434_, v_00_u03b1_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3(lean_object* v_baseMonadInfo_480_, lean_object* v_muts_481_, lean_object* v_base_482_, lean_object* v_dec_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
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
lean_object* v___x_501_; 
lean_inc_ref(v_muts_481_);
v___x_501_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_480_, v_muts_481_, v_resultType_496_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v_restoreCont_503_; lean_object* v___f_504_; uint8_t v___x_505_; lean_object* v___x_507_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v_restoreCont_503_ = lean_ctor_get(v_base_482_, 4);
lean_inc_ref(v_restoreCont_503_);
lean_dec_ref(v_base_482_);
lean_inc(v_a_494_);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed), 12, 4);
lean_closure_set(v___f_504_, 0, v_a_494_);
lean_closure_set(v___f_504_, 1, v_muts_481_);
lean_closure_set(v___f_504_, 2, v_resultName_495_);
lean_closure_set(v___f_504_, 3, v_k_497_);
v___x_505_ = 0;
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 2, v___f_504_);
lean_ctor_set(v___x_499_, 1, v_a_502_);
lean_ctor_set(v___x_499_, 0, v_a_494_);
v___x_507_ = v___x_499_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_a_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v___f_504_);
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
v___x_508_ = lean_apply_9(v_restoreCont_503_, v___x_507_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, lean_box(0));
return v___x_508_;
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_del_object(v___x_499_);
lean_dec_ref(v_k_497_);
lean_dec(v_resultName_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_base_482_);
lean_dec_ref(v_muts_481_);
v_a_510_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_501_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_501_);
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
lean_dec_ref(v_muts_481_);
lean_dec_ref(v_baseMonadInfo_480_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(lean_object* v_baseMonadInfo_527_, lean_object* v_muts_528_, lean_object* v_base_529_, lean_object* v_dec_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(v_baseMonadInfo_527_, v_muts_528_, v_base_529_, v_dec_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
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
lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_v_552_ = lean_array_uget_borrowed(v_bs_542_, v_i_541_);
v___x_553_ = l_Lean_Elab_Do_MutVar_getId(v_v_552_);
v___x_554_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_553_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v_ident_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v_ident_556_ = lean_ctor_get(v_v_552_, 0);
v___x_557_ = l_Lean_LocalDecl_toExpr(v_a_555_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_box(0);
v___x_560_ = 0;
lean_inc_ref(v___x_557_);
lean_inc(v_ident_556_);
v___x_561_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_556_, v___x_557_, v___x_558_, v___x_558_, v___x_559_, v___x_560_, v___x_560_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; lean_object* v_bs_x27_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
lean_dec_ref_known(v___x_561_, 1);
v___x_562_ = lean_unsigned_to_nat(0u);
v_bs_x27_563_ = lean_array_uset(v_bs_542_, v_i_541_, v___x_562_);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_541_, v___x_564_);
v___x_566_ = lean_array_uset(v_bs_x27_563_, v_i_541_, v___x_557_);
v_i_541_ = v___x_565_;
v_bs_542_ = v___x_566_;
goto _start;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref(v___x_557_);
lean_dec_ref(v_bs_542_);
v_a_568_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_561_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_561_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_bs_542_);
v_a_576_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_554_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_554_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_bs_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
size_t v_sz_boxed_594_; size_t v_i_boxed_595_; lean_object* v_res_596_; 
v_sz_boxed_594_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_595_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_594_, v_i_boxed_595_, v_bs_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object* v_muts_606_, lean_object* v_baseMonadInfo_607_, lean_object* v_00_u03c3_608_, lean_object* v_base_609_, lean_object* v_e_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
size_t v_sz_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_sz_619_ = lean_array_size(v_muts_606_);
v___x_620_ = ((size_t)0ULL);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_619_, v___x_620_, v_muts_606_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v_u_623_; lean_object* v___x_624_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v_u_623_ = lean_ctor_get(v_baseMonadInfo_607_, 1);
lean_inc(v_u_623_);
lean_dec_ref(v_baseMonadInfo_607_);
v___x_624_ = l_Lean_Meta_mkProdMkN(v_a_622_, v_u_623_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_673_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_fst_626_ = lean_ctor_get(v_a_625_, 0);
v_snd_627_ = lean_ctor_get(v_a_625_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_a_625_);
if (v_isSharedCheck_673_ == 0)
{
v___x_629_ = v_a_625_;
v_isShared_630_ = v_isSharedCheck_673_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec(v_a_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_673_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___x_642_; 
lean_inc_ref(v_00_u03c3_608_);
lean_inc(v_snd_627_);
v___x_642_ = l_Lean_Meta_isExprDefEq(v_snd_627_, v_00_u03c3_608_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; uint8_t v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = lean_unbox(v_a_643_);
lean_dec(v_a_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
lean_dec(v_fst_626_);
lean_dec_ref(v_e_610_);
lean_dec_ref(v_base_609_);
v___x_645_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1);
v___x_646_ = l_Lean_MessageData_ofExpr(v_00_u03c3_608_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 7);
lean_ctor_set(v___x_629_, 1, v___x_646_);
lean_ctor_set(v___x_629_, 0, v___x_645_);
v___x_648_ = v___x_629_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_664_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v___x_649_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l_Lean_MessageData_ofExpr(v_snd_627_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_654_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_del_object(v___x_629_);
lean_dec(v_snd_627_);
lean_dec_ref(v_00_u03c3_608_);
v___y_632_ = v___y_611_;
v___y_633_ = v___y_612_;
v___y_634_ = v___y_613_;
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
v___y_637_ = v___y_616_;
v___y_638_ = v___y_617_;
goto v___jp_631_;
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_del_object(v___x_629_);
lean_dec(v_snd_627_);
lean_dec(v_fst_626_);
lean_dec_ref(v_e_610_);
lean_dec_ref(v_base_609_);
lean_dec_ref(v_00_u03c3_608_);
v_a_665_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_642_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_642_);
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
v___jp_631_:
{
lean_object* v_runInBase_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_runInBase_639_ = lean_ctor_get(v_base_609_, 3);
lean_inc_ref(v_runInBase_639_);
lean_dec_ref(v_base_609_);
v___x_640_ = l_Lean_Expr_app___override(v_e_610_, v_fst_626_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc_ref(v___y_632_);
v___x_641_ = lean_apply_9(v_runInBase_639_, v___x_640_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, lean_box(0));
return v___x_641_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_e_610_);
lean_dec_ref(v_base_609_);
lean_dec_ref(v_00_u03c3_608_);
v_a_674_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_624_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_624_);
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
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_e_610_);
lean_dec_ref(v_base_609_);
lean_dec_ref(v_00_u03c3_608_);
lean_dec_ref(v_baseMonadInfo_607_);
v_a_682_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_621_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_621_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object* v_muts_690_, lean_object* v_baseMonadInfo_691_, lean_object* v_00_u03c3_692_, lean_object* v_base_693_, lean_object* v_e_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_muts_690_, v_baseMonadInfo_691_, v_00_u03c3_692_, v_base_693_, v_e_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object* v_baseMonadInfo_707_, lean_object* v_muts_708_, lean_object* v_base_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
lean_inc_ref(v_baseMonadInfo_707_);
v___x_718_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_707_, v_muts_708_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v_m_720_; lean_object* v___x_721_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v_m_720_ = lean_ctor_get(v_base_709_, 1);
lean_inc_ref(v_m_720_);
lean_dec_ref(v_base_709_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc_ref(v___y_710_);
v___x_721_ = lean_apply_8(v_m_720_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, lean_box(0));
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_737_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_u_726_; lean_object* v_v_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v_u_726_ = lean_ctor_get(v_baseMonadInfo_707_, 1);
lean_inc(v_u_726_);
v_v_727_ = lean_ctor_get(v_baseMonadInfo_707_, 2);
lean_inc(v_v_727_);
lean_dec_ref(v_baseMonadInfo_707_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1));
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v_v_727_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v_u_726_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_mkConst(v___x_728_, v___x_731_);
v___x_733_ = l_Lean_mkAppB(v___x_732_, v_a_719_, v_a_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_733_);
v___x_735_ = v___x_724_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_dec(v_a_719_);
lean_dec_ref(v_baseMonadInfo_707_);
return v___x_721_;
}
}
else
{
lean_dec_ref(v_base_709_);
lean_dec_ref(v_baseMonadInfo_707_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object* v_baseMonadInfo_738_, lean_object* v_muts_739_, lean_object* v_base_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_738_, v_muts_739_, v_base_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object* v_baseMonadInfo_750_, lean_object* v_muts_751_, lean_object* v_00_u03c3_752_, lean_object* v_base_753_){
_start:
{
lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___x_759_; 
lean_inc_ref(v_00_u03c3_752_);
lean_inc_ref_n(v_base_753_, 4);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0), 3, 2);
lean_closure_set(v___f_754_, 0, v_base_753_);
lean_closure_set(v___f_754_, 1, v_00_u03c3_752_);
lean_inc_ref_n(v_muts_751_, 3);
lean_inc_ref_n(v_baseMonadInfo_750_, 3);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed), 12, 3);
lean_closure_set(v___f_755_, 0, v_baseMonadInfo_750_);
lean_closure_set(v___f_755_, 1, v_muts_751_);
lean_closure_set(v___f_755_, 2, v_base_753_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed), 12, 3);
lean_closure_set(v___f_756_, 0, v_baseMonadInfo_750_);
lean_closure_set(v___f_756_, 1, v_muts_751_);
lean_closure_set(v___f_756_, 2, v_base_753_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed), 13, 4);
lean_closure_set(v___f_757_, 0, v_muts_751_);
lean_closure_set(v___f_757_, 1, v_baseMonadInfo_750_);
lean_closure_set(v___f_757_, 2, v_00_u03c3_752_);
lean_closure_set(v___f_757_, 3, v_base_753_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed), 11, 3);
lean_closure_set(v___f_758_, 0, v_baseMonadInfo_750_);
lean_closure_set(v___f_758_, 1, v_muts_751_);
lean_closure_set(v___f_758_, 2, v_base_753_);
v___x_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_759_, 0, v___f_754_);
lean_ctor_set(v___x_759_, 1, v___f_758_);
lean_ctor_set(v___x_759_, 2, v___f_755_);
lean_ctor_set(v___x_759_, 3, v___f_757_);
lean_ctor_set(v___x_759_, 4, v___f_756_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t v_sz_760_, size_t v_i_761_, lean_object* v_bs_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_760_, v_i_761_, v_bs_762_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object* v_sz_772_, lean_object* v_i_773_, lean_object* v_bs_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
size_t v_sz_boxed_783_; size_t v_i_boxed_784_; lean_object* v_res_785_; 
v_sz_boxed_783_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_784_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_783_, v_i_boxed_784_, v_bs_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object* v_baseMonadInfo_789_, lean_object* v_00_u03b1_790_){
_start:
{
lean_object* v_u_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_u_791_ = lean_ctor_get(v_baseMonadInfo_789_, 1);
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_793_ = lean_box(0);
lean_inc(v_u_791_);
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v_u_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_mkConst(v___x_792_, v___x_794_);
v___x_796_ = l_Lean_Expr_app___override(v___x_795_, v_00_u03b1_790_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object* v_baseMonadInfo_797_, lean_object* v_00_u03b1_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_797_, v_00_u03b1_798_);
lean_dec_ref(v_baseMonadInfo_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object* v_runInBase_805_, lean_object* v_e_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_815_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2));
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_mk_empty_array_with_capacity(v___x_816_);
v___x_818_ = lean_array_push(v___x_817_, v_e_806_);
v___x_819_ = l_Lean_Meta_mkAppM(v___x_815_, v___x_818_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc_ref(v___y_807_);
v___x_821_ = lean_apply_9(v_runInBase_805_, v_a_820_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, lean_box(0));
return v___x_821_;
}
else
{
lean_dec_ref(v_runInBase_805_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object* v_runInBase_822_, lean_object* v_e_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_822_, v_e_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_832_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object* v_description_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1, &l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1);
v___x_839_ = lean_box(0);
v___x_840_ = lean_apply_1(v_description_836_, v___x_839_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_838_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object* v_k_842_, lean_object* v_r_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; 
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc_ref(v___y_844_);
v___x_852_ = lean_apply_8(v_k_842_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, lean_box(0));
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_mk_empty_array_with_capacity(v___x_854_);
v___x_856_ = lean_array_push(v___x_855_, v_r_843_);
v___x_857_ = 0;
v___x_858_ = 1;
v___x_859_ = 1;
v___x_860_ = l_Lean_Meta_mkLambdaFVars(v___x_856_, v_a_853_, v___x_857_, v___x_858_, v___x_857_, v___x_858_, v___x_859_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec_ref(v___x_856_);
return v___x_860_;
}
else
{
lean_dec_ref(v_r_843_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object* v_k_861_, lean_object* v_r_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_k_861_, v_r_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object* v_a_872_, lean_object* v_r_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc_ref(v___y_874_);
v___x_882_ = lean_apply_8(v_a_872_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; uint8_t v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_mk_empty_array_with_capacity(v___x_884_);
v___x_886_ = lean_array_push(v___x_885_, v_r_873_);
v___x_887_ = 0;
v___x_888_ = 1;
v___x_889_ = 1;
v___x_890_ = l_Lean_Meta_mkLambdaFVars(v___x_886_, v_a_883_, v___x_887_, v___x_888_, v___x_887_, v___x_888_, v___x_889_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec_ref(v___x_886_);
return v___x_890_;
}
else
{
lean_dec_ref(v_r_873_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object* v_a_891_, lean_object* v_r_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_891_, v_r_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object* v_k_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_912_ = lean_apply_9(v_k_902_, v_b_906_, v___y_903_, v___y_904_, v___y_905_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, lean_box(0));
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_913_, v___y_914_, v___y_915_, v___y_916_, v_b_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object* v_name_924_, uint8_t v_bi_925_, lean_object* v_type_926_, lean_object* v_k_927_, uint8_t v_kind_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_938_; 
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc_ref(v___y_929_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_937_, 0, v_k_927_);
lean_closure_set(v___f_937_, 1, v___y_929_);
lean_closure_set(v___f_937_, 2, v___y_930_);
lean_closure_set(v___f_937_, 3, v___y_931_);
v___x_938_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_924_, v_bi_925_, v_type_926_, v___f_937_, v_kind_928_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_938_) == 0)
{
return v___x_938_;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object* v_name_947_, lean_object* v_bi_948_, lean_object* v_type_949_, lean_object* v_k_950_, lean_object* v_kind_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_bi_boxed_960_; uint8_t v_kind_boxed_961_; lean_object* v_res_962_; 
v_bi_boxed_960_ = lean_unbox(v_bi_948_);
v_kind_boxed_961_ = lean_unbox(v_kind_951_);
v_res_962_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_947_, v_bi_boxed_960_, v_type_949_, v_k_950_, v_kind_boxed_961_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object* v_name_963_, lean_object* v_type_964_, lean_object* v_k_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; 
v___x_974_ = 0;
v___x_975_ = 0;
v___x_976_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_963_, v___x_974_, v_type_964_, v_k_965_, v___x_975_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object* v_name_977_, lean_object* v_type_978_, lean_object* v_k_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_977_, v_type_978_, v_k_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3));
v___x_997_ = l_Lean_mkConst(v___x_996_, v___x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object* v_a_998_, lean_object* v_getCont_999_, lean_object* v_resultName_1000_, lean_object* v_resultType_1001_, lean_object* v___f_1002_, lean_object* v_baseMonadInfo_1003_, lean_object* v_casesOnWrapper_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_getFVarFromUserName(v_a_998_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc_ref(v___y_1005_);
v___x_1015_ = lean_apply_8(v_getCont_999_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, lean_box(0));
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1018_ = l_Lean_Core_mkFreshUserName(v___x_1017_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1020_, 0, v_a_1016_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4, &l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4);
v___x_1023_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1019_, v___x_1022_, v___f_1020_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
lean_inc_ref(v_resultType_1001_);
v___x_1025_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1000_, v_resultType_1001_, v___f_1002_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_doBlockResultType_1027_; lean_object* v___x_1028_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_doBlockResultType_1027_ = lean_ctor_get(v___y_1005_, 3);
lean_inc_ref(v_doBlockResultType_1027_);
v___x_1028_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1027_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_u_1033_; lean_object* v_v_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v_u_1033_ = lean_ctor_get(v_baseMonadInfo_1003_, 1);
v_v_1034_ = lean_ctor_get(v_baseMonadInfo_1003_, 2);
lean_inc(v_v_1034_);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_v_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1021_);
lean_inc(v_u_1033_);
v___x_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_u_1033_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_mkConst(v_casesOnWrapper_1004_, v___x_1036_);
v___x_1038_ = l_Lean_mkApp5(v___x_1037_, v_resultType_1001_, v_a_1029_, v_a_1014_, v_a_1024_, v_a_1026_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1038_);
v___x_1040_ = v___x_1031_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_dec(v_a_1026_);
lean_dec(v_a_1024_);
lean_dec(v_a_1014_);
lean_dec(v_casesOnWrapper_1004_);
lean_dec_ref(v_resultType_1001_);
return v___x_1028_;
}
}
else
{
lean_dec(v_a_1024_);
lean_dec(v_a_1014_);
lean_dec(v_casesOnWrapper_1004_);
lean_dec_ref(v_resultType_1001_);
return v___x_1025_;
}
}
else
{
lean_dec(v_a_1014_);
lean_dec(v_casesOnWrapper_1004_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v_resultType_1001_);
lean_dec(v_resultName_1000_);
return v___x_1023_;
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_a_1016_);
lean_dec(v_a_1014_);
lean_dec(v_casesOnWrapper_1004_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v_resultType_1001_);
lean_dec(v_resultName_1000_);
v_a_1043_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1018_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1018_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1014_);
lean_dec(v_casesOnWrapper_1004_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v_resultType_1001_);
lean_dec(v_resultName_1000_);
v_a_1051_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1015_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1015_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_dec(v_casesOnWrapper_1004_);
lean_dec_ref(v___f_1002_);
lean_dec_ref(v_resultType_1001_);
lean_dec(v_resultName_1000_);
lean_dec_ref(v_getCont_999_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object* v_a_1059_, lean_object* v_getCont_1060_, lean_object* v_resultName_1061_, lean_object* v_resultType_1062_, lean_object* v___f_1063_, lean_object* v_baseMonadInfo_1064_, lean_object* v_casesOnWrapper_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1059_, v_getCont_1060_, v_resultName_1061_, v_resultType_1062_, v___f_1063_, v_baseMonadInfo_1064_, v_casesOnWrapper_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v_baseMonadInfo_1064_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object* v_getCont_1078_, lean_object* v_baseMonadInfo_1079_, lean_object* v_casesOnWrapper_1080_, lean_object* v_restoreCont_1081_, lean_object* v_dec_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1092_ = l_Lean_Core_mkFreshUserName(v___x_1091_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v_resultName_1094_; lean_object* v_resultType_1095_; lean_object* v_k_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1108_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v_resultName_1094_ = lean_ctor_get(v_dec_1082_, 0);
v_resultType_1095_ = lean_ctor_get(v_dec_1082_, 1);
v_k_1096_ = lean_ctor_get(v_dec_1082_, 2);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_dec_1082_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1098_ = v_dec_1082_;
v_isShared_1099_ = v_isSharedCheck_1108_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_k_1096_);
lean_inc(v_resultType_1095_);
lean_inc(v_resultName_1094_);
lean_dec(v_dec_1082_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1108_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___f_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1105_; 
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1100_, 0, v_k_1096_);
lean_inc_ref(v_baseMonadInfo_1079_);
lean_inc_ref(v_resultType_1095_);
lean_inc(v_a_1093_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed), 15, 7);
lean_closure_set(v___f_1101_, 0, v_a_1093_);
lean_closure_set(v___f_1101_, 1, v_getCont_1078_);
lean_closure_set(v___f_1101_, 2, v_resultName_1094_);
lean_closure_set(v___f_1101_, 3, v_resultType_1095_);
lean_closure_set(v___f_1101_, 4, v___f_1100_);
lean_closure_set(v___f_1101_, 5, v_baseMonadInfo_1079_);
lean_closure_set(v___f_1101_, 6, v_casesOnWrapper_1080_);
v___x_1102_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1079_, v_resultType_1095_);
lean_dec_ref(v_baseMonadInfo_1079_);
v___x_1103_ = 0;
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v___f_1101_);
lean_ctor_set(v___x_1098_, 1, v___x_1102_);
lean_ctor_set(v___x_1098_, 0, v_a_1093_);
v___x_1105_ = v___x_1098_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1093_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v___f_1101_);
v___x_1105_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*3, v___x_1103_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc_ref(v___y_1083_);
v___x_1106_ = lean_apply_9(v_restoreCont_1081_, v___x_1105_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, lean_box(0));
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_dec_1082_);
lean_dec_ref(v_restoreCont_1081_);
lean_dec(v_casesOnWrapper_1080_);
lean_dec_ref(v_baseMonadInfo_1079_);
lean_dec_ref(v_getCont_1078_);
v_a_1109_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1092_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1092_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object* v_getCont_1117_, lean_object* v_baseMonadInfo_1118_, lean_object* v_casesOnWrapper_1119_, lean_object* v_restoreCont_1120_, lean_object* v_dec_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1117_, v_baseMonadInfo_1118_, v_casesOnWrapper_1119_, v_restoreCont_1120_, v_dec_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object* v_baseMonadInfo_1131_, lean_object* v_stM_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1131_, v___y_1133_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc_ref(v___y_1134_);
v___x_1143_ = lean_apply_9(v_stM_1132_, v___x_1142_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, lean_box(0));
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object* v_baseMonadInfo_1144_, lean_object* v_stM_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1144_, v_stM_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_baseMonadInfo_1144_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object* v_m_1156_, lean_object* v_baseMonadInfo_1157_, lean_object* v_optionTWrapper_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc_ref(v___y_1159_);
v___x_1167_ = lean_apply_8(v_m_1156_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, lean_box(0));
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1182_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1182_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1182_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_u_1172_; lean_object* v_v_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v_u_1172_ = lean_ctor_get(v_baseMonadInfo_1157_, 1);
v_v_1173_ = lean_ctor_get(v_baseMonadInfo_1157_, 2);
v___x_1174_ = lean_box(0);
lean_inc(v_v_1173_);
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_v_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_inc(v_u_1172_);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_u_1172_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_mkConst(v_optionTWrapper_1158_, v___x_1176_);
v___x_1178_ = l_Lean_Expr_app___override(v___x_1177_, v_a_1168_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1178_);
v___x_1180_ = v___x_1170_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_dec(v_optionTWrapper_1158_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object* v_m_1183_, lean_object* v_baseMonadInfo_1184_, lean_object* v_optionTWrapper_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1183_, v_baseMonadInfo_1184_, v_optionTWrapper_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_baseMonadInfo_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object* v_baseMonadInfo_1195_, lean_object* v_optionTWrapper_1196_, lean_object* v_casesOnWrapper_1197_, lean_object* v_getCont_1198_, lean_object* v_base_1199_){
_start:
{
lean_object* v_description_1200_; lean_object* v_m_1201_; lean_object* v_stM_1202_; lean_object* v_runInBase_1203_; lean_object* v_restoreCont_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1216_; 
v_description_1200_ = lean_ctor_get(v_base_1199_, 0);
v_m_1201_ = lean_ctor_get(v_base_1199_, 1);
v_stM_1202_ = lean_ctor_get(v_base_1199_, 2);
v_runInBase_1203_ = lean_ctor_get(v_base_1199_, 3);
v_restoreCont_1204_ = lean_ctor_get(v_base_1199_, 4);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_base_1199_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1206_ = v_base_1199_;
v_isShared_1207_ = v_isSharedCheck_1216_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_restoreCont_1204_);
lean_inc(v_runInBase_1203_);
lean_inc(v_stM_1202_);
lean_inc(v_m_1201_);
lean_inc(v_description_1200_);
lean_dec(v_base_1199_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1216_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v___x_1214_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1208_, 0, v_runInBase_1203_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1), 2, 1);
lean_closure_set(v___f_1209_, 0, v_description_1200_);
lean_inc_ref_n(v_baseMonadInfo_1195_, 2);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed), 13, 4);
lean_closure_set(v___f_1210_, 0, v_getCont_1198_);
lean_closure_set(v___f_1210_, 1, v_baseMonadInfo_1195_);
lean_closure_set(v___f_1210_, 2, v_casesOnWrapper_1197_);
lean_closure_set(v___f_1210_, 3, v_restoreCont_1204_);
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed), 11, 2);
lean_closure_set(v___f_1211_, 0, v_baseMonadInfo_1195_);
lean_closure_set(v___f_1211_, 1, v_stM_1202_);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed), 11, 3);
lean_closure_set(v___f_1212_, 0, v_m_1201_);
lean_closure_set(v___f_1212_, 1, v_baseMonadInfo_1195_);
lean_closure_set(v___f_1212_, 2, v_optionTWrapper_1196_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 4, v___f_1210_);
lean_ctor_set(v___x_1206_, 3, v___f_1208_);
lean_ctor_set(v___x_1206_, 2, v___f_1211_);
lean_ctor_set(v___x_1206_, 1, v___f_1212_);
lean_ctor_set(v___x_1206_, 0, v___f_1209_);
v___x_1214_ = v___x_1206_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___f_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___f_1212_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v___f_1211_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v___f_1208_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v___f_1210_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object* v_00_u03b1_1217_, lean_object* v_name_1218_, uint8_t v_bi_1219_, lean_object* v_type_1220_, lean_object* v_k_1221_, uint8_t v_kind_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_1218_, v_bi_1219_, v_type_1220_, v_k_1221_, v_kind_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_name_1233_, lean_object* v_bi_1234_, lean_object* v_type_1235_, lean_object* v_k_1236_, lean_object* v_kind_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_bi_boxed_1246_; uint8_t v_kind_boxed_1247_; lean_object* v_res_1248_; 
v_bi_boxed_1246_ = lean_unbox(v_bi_1234_);
v_kind_boxed_1247_ = lean_unbox(v_kind_1237_);
v_res_1248_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_1232_, v_name_1233_, v_bi_boxed_1246_, v_type_1235_, v_k_1236_, v_kind_boxed_1247_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object* v_00_u03b1_1249_, lean_object* v_name_1250_, lean_object* v_type_1251_, lean_object* v_k_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1250_, v_type_1251_, v_k_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_name_1263_, lean_object* v_type_1264_, lean_object* v_k_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(v_00_u03b1_1262_, v_name_1263_, v_type_1264_, v_k_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object* v_baseMonadInfo_1278_, lean_object* v_getCont_1279_, lean_object* v_00_u03b1_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1289_; 
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
lean_inc(v_a_1285_);
lean_inc_ref(v_a_1284_);
lean_inc(v_a_1283_);
lean_inc_ref(v_a_1282_);
lean_inc_ref(v_a_1281_);
v___x_1289_ = lean_apply_8(v_getCont_1279_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, lean_box(0));
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1312_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1312_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1312_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_u_1294_; lean_object* v_resultType_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1310_; 
v_u_1294_ = lean_ctor_get(v_baseMonadInfo_1278_, 1);
v_resultType_1295_ = lean_ctor_get(v_a_1290_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1290_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v_a_1290_, 1);
lean_dec(v_unused_1311_);
v___x_1297_ = v_a_1290_;
v_isShared_1298_ = v_isSharedCheck_1310_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_resultType_1295_);
lean_dec(v_a_1290_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1310_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_box(0);
lean_inc(v_u_1294_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 1);
lean_ctor_set(v___x_1297_, 1, v___x_1299_);
lean_ctor_set(v___x_1297_, 0, v_u_1294_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_u_1294_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
lean_inc(v_u_1294_);
v___x_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1303_, 0, v_u_1294_);
lean_ctor_set(v___x_1303_, 1, v___x_1301_);
v___x_1304_ = l_Lean_mkConst(v___x_1302_, v___x_1303_);
v___x_1305_ = l_Lean_mkAppB(v___x_1304_, v_resultType_1295_, v_00_u03b1_1280_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1305_);
v___x_1307_ = v___x_1292_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_00_u03b1_1280_);
v_a_1313_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1289_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1289_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object* v_baseMonadInfo_1321_, lean_object* v_getCont_1322_, lean_object* v_00_u03b1_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1321_, v_getCont_1322_, v_00_u03b1_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_baseMonadInfo_1321_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object* v_k_1333_, lean_object* v_r_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc_ref(v___y_1335_);
v___x_1343_ = lean_apply_8(v_k_1333_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, lean_box(0));
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_n(v_a_1344_, 2);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_mk_empty_array_with_capacity(v___x_1345_);
v___x_1347_ = lean_array_push(v___x_1346_, v_r_1334_);
v___x_1348_ = 0;
v___x_1349_ = 1;
v___x_1350_ = 1;
v___x_1351_ = l_Lean_Meta_mkLambdaFVars(v___x_1347_, v_a_1344_, v___x_1348_, v___x_1349_, v___x_1348_, v___x_1349_, v___x_1350_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec_ref(v___x_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1353_ = lean_infer_type(v_a_1344_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1362_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1362_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1352_);
lean_ctor_set(v___x_1358_, 1, v_a_1354_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1352_);
v_a_1363_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1353_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1353_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_a_1344_);
v_a_1371_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1351_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1351_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v_r_1334_);
v_a_1379_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1343_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1343_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object* v_k_1387_, lean_object* v_r_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_k_1387_, v_r_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object* v_k_1398_, lean_object* v_r_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc_ref(v_r_1399_);
v___x_1408_ = lean_apply_9(v_k_1398_, v_r_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; uint8_t v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_mk_empty_array_with_capacity(v___x_1410_);
v___x_1412_ = lean_array_push(v___x_1411_, v_r_1399_);
v___x_1413_ = 0;
v___x_1414_ = 1;
v___x_1415_ = 1;
v___x_1416_ = l_Lean_Meta_mkLambdaFVars(v___x_1412_, v_a_1409_, v___x_1413_, v___x_1414_, v___x_1413_, v___x_1414_, v___x_1415_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec_ref(v___x_1412_);
return v___x_1416_;
}
else
{
lean_dec_ref(v_r_1399_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object* v_k_1417_, lean_object* v_r_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_k_1417_, v_r_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object* v_a_1428_, lean_object* v_getCont_1429_, lean_object* v_resultName_1430_, lean_object* v_resultType_1431_, lean_object* v___f_1432_, lean_object* v_baseMonadInfo_1433_, lean_object* v_casesOnWrapper_1434_, lean_object* v_00_u03b5_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Meta_getFVarFromUserName(v_a_1428_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1446_ = lean_apply_8(v_getCont_1429_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, lean_box(0));
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1449_ = l_Lean_Core_mkFreshUserName(v___x_1448_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v_resultType_1451_; lean_object* v_k_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1493_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v_resultType_1451_ = lean_ctor_get(v_a_1447_, 0);
v_k_1452_ = lean_ctor_get(v_a_1447_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_a_1447_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1454_ = v_a_1447_;
v_isShared_1455_ = v_isSharedCheck_1493_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_k_1452_);
lean_inc(v_resultType_1451_);
lean_dec(v_a_1447_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1493_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___f_1456_; lean_object* v___x_1457_; 
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1456_, 0, v_k_1452_);
v___x_1457_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1450_, v_resultType_1451_, v___f_1456_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
lean_inc_ref(v_resultType_1431_);
v___x_1459_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1430_, v_resultType_1431_, v___f_1432_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1484_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1484_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1484_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_fst_1464_; lean_object* v_snd_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1483_; 
v_fst_1464_ = lean_ctor_get(v_a_1460_, 0);
v_snd_1465_ = lean_ctor_get(v_a_1460_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1460_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1467_ = v_a_1460_;
v_isShared_1468_ = v_isSharedCheck_1483_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snd_1465_);
lean_inc(v_fst_1464_);
lean_dec(v_a_1460_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1483_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_u_1469_; lean_object* v_v_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v_u_1469_ = lean_ctor_get(v_baseMonadInfo_1433_, 1);
v_v_1470_ = lean_ctor_get(v_baseMonadInfo_1433_, 2);
v___x_1471_ = lean_box(0);
lean_inc(v_v_1470_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 1);
lean_ctor_set(v___x_1467_, 1, v___x_1471_);
lean_ctor_set(v___x_1467_, 0, v_v_1470_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
lean_inc(v_u_1469_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 1);
lean_ctor_set(v___x_1454_, 1, v___x_1473_);
lean_ctor_set(v___x_1454_, 0, v_u_1469_);
v___x_1475_ = v___x_1454_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_u_1469_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1476_ = l_Lean_mkConst(v_casesOnWrapper_1434_, v___x_1475_);
v___x_1477_ = l_Lean_mkApp6(v___x_1476_, v_00_u03b5_1435_, v_resultType_1431_, v_snd_1465_, v_a_1445_, v_a_1458_, v_fst_1464_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1477_);
v___x_1479_ = v___x_1462_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
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
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1458_);
lean_del_object(v___x_1454_);
lean_dec(v_a_1445_);
lean_dec_ref(v_00_u03b5_1435_);
lean_dec(v_casesOnWrapper_1434_);
lean_dec_ref(v_resultType_1431_);
v_a_1485_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1459_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1459_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
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
else
{
lean_del_object(v___x_1454_);
lean_dec(v_a_1445_);
lean_dec_ref(v_00_u03b5_1435_);
lean_dec(v_casesOnWrapper_1434_);
lean_dec_ref(v___f_1432_);
lean_dec_ref(v_resultType_1431_);
lean_dec(v_resultName_1430_);
return v___x_1457_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_a_1447_);
lean_dec(v_a_1445_);
lean_dec_ref(v_00_u03b5_1435_);
lean_dec(v_casesOnWrapper_1434_);
lean_dec_ref(v___f_1432_);
lean_dec_ref(v_resultType_1431_);
lean_dec(v_resultName_1430_);
v_a_1494_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1449_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1449_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_a_1445_);
lean_dec_ref(v_00_u03b5_1435_);
lean_dec(v_casesOnWrapper_1434_);
lean_dec_ref(v___f_1432_);
lean_dec_ref(v_resultType_1431_);
lean_dec(v_resultName_1430_);
v_a_1502_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1446_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1446_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1435_);
lean_dec(v_casesOnWrapper_1434_);
lean_dec_ref(v___f_1432_);
lean_dec_ref(v_resultType_1431_);
lean_dec(v_resultName_1430_);
lean_dec_ref(v_getCont_1429_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object* v_a_1510_, lean_object* v_getCont_1511_, lean_object* v_resultName_1512_, lean_object* v_resultType_1513_, lean_object* v___f_1514_, lean_object* v_baseMonadInfo_1515_, lean_object* v_casesOnWrapper_1516_, lean_object* v_00_u03b5_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1510_, v_getCont_1511_, v_resultName_1512_, v_resultType_1513_, v___f_1514_, v_baseMonadInfo_1515_, v_casesOnWrapper_1516_, v_00_u03b5_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v_baseMonadInfo_1515_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object* v_baseMonadInfo_1527_, lean_object* v_getCont_1528_, lean_object* v_casesOnWrapper_1529_, lean_object* v_00_u03b5_1530_, lean_object* v_restoreCont_1531_, lean_object* v_dec_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1542_ = l_Lean_Core_mkFreshUserName(v___x_1541_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_resultName_1544_; lean_object* v_resultType_1545_; lean_object* v_k_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1567_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_resultName_1544_ = lean_ctor_get(v_dec_1532_, 0);
v_resultType_1545_ = lean_ctor_get(v_dec_1532_, 1);
v_k_1546_ = lean_ctor_get(v_dec_1532_, 2);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_dec_1532_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1548_ = v_dec_1532_;
v_isShared_1549_ = v_isSharedCheck_1567_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_k_1546_);
lean_inc(v_resultType_1545_);
lean_inc(v_resultName_1544_);
lean_dec(v_dec_1532_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1567_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; 
lean_inc_ref(v_resultType_1545_);
lean_inc_ref(v_getCont_1528_);
v___x_1550_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1527_, v_getCont_1528_, v_resultType_1545_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; uint8_t v___x_1554_; lean_object* v___x_1556_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1552_, 0, v_k_1546_);
lean_inc(v_a_1543_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed), 16, 8);
lean_closure_set(v___f_1553_, 0, v_a_1543_);
lean_closure_set(v___f_1553_, 1, v_getCont_1528_);
lean_closure_set(v___f_1553_, 2, v_resultName_1544_);
lean_closure_set(v___f_1553_, 3, v_resultType_1545_);
lean_closure_set(v___f_1553_, 4, v___f_1552_);
lean_closure_set(v___f_1553_, 5, v_baseMonadInfo_1527_);
lean_closure_set(v___f_1553_, 6, v_casesOnWrapper_1529_);
lean_closure_set(v___f_1553_, 7, v_00_u03b5_1530_);
v___x_1554_ = 0;
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 2, v___f_1553_);
lean_ctor_set(v___x_1548_, 1, v_a_1551_);
lean_ctor_set(v___x_1548_, 0, v_a_1543_);
v___x_1556_ = v___x_1548_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1543_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_a_1551_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v___f_1553_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*3, v___x_1554_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc_ref(v___y_1533_);
v___x_1557_ = lean_apply_9(v_restoreCont_1531_, v___x_1556_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, lean_box(0));
return v___x_1557_;
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1548_);
lean_dec_ref(v_k_1546_);
lean_dec_ref(v_resultType_1545_);
lean_dec(v_resultName_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_restoreCont_1531_);
lean_dec_ref(v_00_u03b5_1530_);
lean_dec(v_casesOnWrapper_1529_);
lean_dec_ref(v_getCont_1528_);
lean_dec_ref(v_baseMonadInfo_1527_);
v_a_1559_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1550_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1550_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_dec_1532_);
lean_dec_ref(v_restoreCont_1531_);
lean_dec_ref(v_00_u03b5_1530_);
lean_dec(v_casesOnWrapper_1529_);
lean_dec_ref(v_getCont_1528_);
lean_dec_ref(v_baseMonadInfo_1527_);
v_a_1568_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1542_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1542_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object* v_baseMonadInfo_1576_, lean_object* v_getCont_1577_, lean_object* v_casesOnWrapper_1578_, lean_object* v_00_u03b5_1579_, lean_object* v_restoreCont_1580_, lean_object* v_dec_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_baseMonadInfo_1576_, v_getCont_1577_, v_casesOnWrapper_1578_, v_00_u03b5_1579_, v_restoreCont_1580_, v_dec_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object* v_00_u03b5_1597_, lean_object* v_description_1598_, lean_object* v_x_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1600_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1);
v___x_1601_ = l_Lean_MessageData_ofExpr(v_00_u03b5_1597_);
v___x_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_apply_1(v_description_1598_, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1604_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object* v_baseMonadInfo_1608_, lean_object* v_getCont_1609_, lean_object* v_stM_1610_, lean_object* v_00_u03b1_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1608_, v_getCont_1609_, v_00_u03b1_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
lean_inc(v___y_1618_);
lean_inc_ref(v___y_1617_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc_ref(v___y_1612_);
v___x_1622_ = lean_apply_9(v_stM_1610_, v_a_1621_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, lean_box(0));
return v___x_1622_;
}
else
{
lean_dec_ref(v_stM_1610_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object* v_baseMonadInfo_1623_, lean_object* v_getCont_1624_, lean_object* v_stM_1625_, lean_object* v_00_u03b1_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1623_, v_getCont_1624_, v_stM_1625_, v_00_u03b1_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v_baseMonadInfo_1623_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object* v_runInBase_1640_, lean_object* v_e_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1650_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1));
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_mk_empty_array_with_capacity(v___x_1651_);
v___x_1653_ = lean_array_push(v___x_1652_, v_e_1641_);
v___x_1654_ = l_Lean_Meta_mkAppM(v___x_1650_, v___x_1653_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc_ref(v___y_1642_);
v___x_1656_ = lean_apply_9(v_runInBase_1640_, v_a_1655_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, lean_box(0));
return v___x_1656_;
}
else
{
lean_dec_ref(v_runInBase_1640_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object* v_runInBase_1657_, lean_object* v_e_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1657_, v_e_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object* v_m_1668_, lean_object* v_baseMonadInfo_1669_, lean_object* v_exceptTWrapper_1670_, lean_object* v_00_u03b5_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc_ref(v___y_1672_);
v___x_1680_ = lean_apply_8(v_m_1668_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, lean_box(0));
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1695_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_u_1685_; lean_object* v_v_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v_u_1685_ = lean_ctor_get(v_baseMonadInfo_1669_, 1);
v_v_1686_ = lean_ctor_get(v_baseMonadInfo_1669_, 2);
v___x_1687_ = lean_box(0);
lean_inc(v_v_1686_);
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_v_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
lean_inc(v_u_1685_);
v___x_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_u_1685_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_mkConst(v_exceptTWrapper_1670_, v___x_1689_);
v___x_1691_ = l_Lean_mkAppB(v___x_1690_, v_00_u03b5_1671_, v_a_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1691_);
v___x_1693_ = v___x_1683_;
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
}
else
{
lean_dec_ref(v_00_u03b5_1671_);
lean_dec(v_exceptTWrapper_1670_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object* v_m_1696_, lean_object* v_baseMonadInfo_1697_, lean_object* v_exceptTWrapper_1698_, lean_object* v_00_u03b5_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1696_, v_baseMonadInfo_1697_, v_exceptTWrapper_1698_, v_00_u03b5_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v_baseMonadInfo_1697_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object* v_baseMonadInfo_1709_, lean_object* v_exceptTWrapper_1710_, lean_object* v_casesOnWrapper_1711_, lean_object* v_getCont_1712_, lean_object* v_00_u03b5_1713_, lean_object* v_base_1714_){
_start:
{
lean_object* v_description_1715_; lean_object* v_m_1716_; lean_object* v_stM_1717_; lean_object* v_runInBase_1718_; lean_object* v_restoreCont_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1731_; 
v_description_1715_ = lean_ctor_get(v_base_1714_, 0);
v_m_1716_ = lean_ctor_get(v_base_1714_, 1);
v_stM_1717_ = lean_ctor_get(v_base_1714_, 2);
v_runInBase_1718_ = lean_ctor_get(v_base_1714_, 3);
v_restoreCont_1719_ = lean_ctor_get(v_base_1714_, 4);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_base_1714_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1721_ = v_base_1714_;
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_restoreCont_1719_);
lean_inc(v_runInBase_1718_);
lean_inc(v_stM_1717_);
lean_inc(v_m_1716_);
lean_inc(v_description_1715_);
lean_dec(v_base_1714_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___x_1729_; 
lean_inc_ref_n(v_00_u03b5_1713_, 2);
lean_inc_ref(v_getCont_1712_);
lean_inc_ref_n(v_baseMonadInfo_1709_, 2);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed), 14, 5);
lean_closure_set(v___f_1723_, 0, v_baseMonadInfo_1709_);
lean_closure_set(v___f_1723_, 1, v_getCont_1712_);
lean_closure_set(v___f_1723_, 2, v_casesOnWrapper_1711_);
lean_closure_set(v___f_1723_, 3, v_00_u03b5_1713_);
lean_closure_set(v___f_1723_, 4, v_restoreCont_1719_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4), 3, 2);
lean_closure_set(v___f_1724_, 0, v_00_u03b5_1713_);
lean_closure_set(v___f_1724_, 1, v_description_1715_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed), 12, 3);
lean_closure_set(v___f_1725_, 0, v_baseMonadInfo_1709_);
lean_closure_set(v___f_1725_, 1, v_getCont_1712_);
lean_closure_set(v___f_1725_, 2, v_stM_1717_);
v___f_1726_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed), 10, 1);
lean_closure_set(v___f_1726_, 0, v_runInBase_1718_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed), 12, 4);
lean_closure_set(v___f_1727_, 0, v_m_1716_);
lean_closure_set(v___f_1727_, 1, v_baseMonadInfo_1709_);
lean_closure_set(v___f_1727_, 2, v_exceptTWrapper_1710_);
lean_closure_set(v___f_1727_, 3, v_00_u03b5_1713_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 4, v___f_1723_);
lean_ctor_set(v___x_1721_, 3, v___f_1726_);
lean_ctor_set(v___x_1721_, 2, v___f_1725_);
lean_ctor_set(v___x_1721_, 1, v___f_1727_);
lean_ctor_set(v___x_1721_, 0, v___f_1724_);
v___x_1729_ = v___x_1721_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___f_1724_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___f_1727_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v___f_1725_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v___f_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v___f_1723_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object* v_baseMonadInfo_1741_, lean_object* v_00_u03c1_1742_, lean_object* v_m_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1));
v___x_1745_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4));
v___x_1746_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5));
v___x_1747_ = l_Lean_Elab_Do_ControlStack_exceptT(v_baseMonadInfo_1741_, v___x_1744_, v___x_1745_, v___x_1746_, v_00_u03c1_1742_, v_m_1743_);
return v___x_1747_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0));
v___x_1750_ = l_Lean_stringToMessageData(v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_1751_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1770_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
if (lean_obj_tag(v_a_1760_) == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_del_object(v___x_1762_);
v___x_1764_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1);
v___x_1765_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1764_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1765_;
}
else
{
lean_object* v_val_1766_; lean_object* v___x_1768_; 
v_val_1766_ = lean_ctor_get(v_a_1760_, 0);
lean_inc(v_val_1766_);
lean_dec_ref_known(v_a_1760_, 1);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v_val_1766_);
v___x_1768_ = v___x_1762_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_val_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1759_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1759_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1779_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object* v_baseMonadInfo_1796_, lean_object* v_m_1797_){
_start:
{
lean_object* v_getCont_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_getCont_1798_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__0));
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__2));
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__4));
v___x_1801_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1796_, v___x_1799_, v___x_1800_, v_getCont_1798_, v_m_1797_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_1805_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1824_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1824_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1824_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
if (lean_obj_tag(v_a_1814_) == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1816_);
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1);
v___x_1819_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1818_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1822_; 
v_val_1820_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v_a_1814_, 1);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_val_1820_);
v___x_1822_ = v___x_1816_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_val_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1813_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1813_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object* v_baseMonadInfo_1850_, lean_object* v_m_1851_){
_start:
{
lean_object* v_getCont_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_getCont_1852_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__0));
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__2));
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__4));
v___x_1855_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1850_, v___x_1853_, v___x_1854_, v_getCont_1852_, v_m_1851_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object* v_mi_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_m_1867_; lean_object* v_u_1868_; lean_object* v_v_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_m_1867_ = lean_ctor_get(v_mi_1859_, 0);
lean_inc_ref(v_m_1867_);
v_u_1868_ = lean_ctor_get(v_mi_1859_, 1);
lean_inc(v_u_1868_);
v_v_1869_ = lean_ctor_get(v_mi_1859_, 2);
lean_inc(v_v_1869_);
lean_dec_ref(v_mi_1859_);
v___x_1870_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1));
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_v_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_u_1868_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_mkConst(v___x_1870_, v___x_1873_);
v___x_1875_ = l_Lean_Expr_app___override(v___x_1874_, v_m_1867_);
v___x_1876_ = lean_box(0);
v___x_1877_ = l_Lean_Elab_Term_mkInstMVar(v___x_1875_, v___x_1876_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object* v_mi_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
return v_res_1886_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0));
v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2));
v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4));
v___x_1895_ = l_Lean_stringToMessageData(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6));
v___x_1898_ = l_Lean_stringToMessageData(v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object* v_msg_1899_, lean_object* v_expected_1900_, lean_object* v_actual_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v___x_1907_; 
lean_inc_ref(v_actual_1901_);
lean_inc_ref(v_expected_1900_);
v___x_1907_ = l_Lean_Meta_isExprDefEq(v_expected_1900_, v_actual_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1931_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1931_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1931_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_unbox(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_del_object(v___x_1910_);
v___x_1913_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
v___x_1914_ = l_Lean_stringToMessageData(v_msg_1899_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_MessageData_ofExpr(v_expected_1900_);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = l_Lean_MessageData_ofExpr(v_actual_1901_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1925_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
return v___x_1926_;
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
lean_dec_ref(v_actual_1901_);
lean_dec_ref(v_expected_1900_);
lean_dec_ref(v_msg_1899_);
v___x_1927_ = lean_box(0);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1927_);
v___x_1929_ = v___x_1910_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_actual_1901_);
lean_dec_ref(v_expected_1900_);
lean_dec_ref(v_msg_1899_);
v_a_1932_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1907_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1907_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object* v_msg_1940_, lean_object* v_expected_1941_, lean_object* v_actual_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1940_, v_expected_1941_, v_actual_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object* v_msg_1949_, lean_object* v_expected_1950_, lean_object* v_actual_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1949_, v_expected_1950_, v_actual_1951_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object* v_msg_1961_, lean_object* v_expected_1962_, lean_object* v_actual_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_1961_, v_expected_1962_, v_actual_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object* v_base_1978_, uint8_t v_hasContinue_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_m_1988_; lean_object* v_runInBase_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2047_; 
v_m_1988_ = lean_ctor_get(v_base_1978_, 1);
v_runInBase_1989_ = lean_ctor_get(v_base_1978_, 3);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_base_1978_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; 
v_unused_2048_ = lean_ctor_get(v_base_1978_, 4);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_base_1978_, 2);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_base_1978_, 0);
lean_dec(v_unused_2050_);
v___x_1991_ = v_base_1978_;
v_isShared_1992_ = v_isSharedCheck_2047_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_runInBase_1989_);
lean_inc(v_m_1988_);
lean_dec(v_base_1978_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2047_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; 
lean_inc(v_a_1986_);
lean_inc_ref(v_a_1985_);
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc_ref(v_a_1980_);
v___x_1993_ = lean_apply_8(v_m_1988_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, lean_box(0));
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_monadInfo_1994_; lean_object* v_a_1995_; lean_object* v_doBlockResultType_1996_; lean_object* v_u_1997_; lean_object* v_v_1998_; lean_object* v_cachedPUnit_1999_; lean_object* v_cachedPUnitUnit_2000_; lean_object* v___x_2002_; 
v_monadInfo_1994_ = lean_ctor_get(v_a_1980_, 0);
v_a_1995_ = lean_ctor_get(v___x_1993_, 0);
lean_inc_n(v_a_1995_, 2);
lean_dec_ref_known(v___x_1993_, 1);
v_doBlockResultType_1996_ = lean_ctor_get(v_a_1980_, 3);
v_u_1997_ = lean_ctor_get(v_monadInfo_1994_, 1);
v_v_1998_ = lean_ctor_get(v_monadInfo_1994_, 2);
v_cachedPUnit_1999_ = lean_ctor_get(v_monadInfo_1994_, 3);
v_cachedPUnitUnit_2000_ = lean_ctor_get(v_monadInfo_1994_, 4);
lean_inc_ref(v_cachedPUnitUnit_2000_);
lean_inc_ref(v_cachedPUnit_1999_);
lean_inc(v_v_1998_);
lean_inc(v_u_1997_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v_cachedPUnitUnit_2000_);
lean_ctor_set(v___x_1991_, 3, v_cachedPUnit_1999_);
lean_ctor_set(v___x_1991_, 2, v_v_1998_);
lean_ctor_set(v___x_1991_, 1, v_u_1997_);
lean_ctor_set(v___x_1991_, 0, v_a_1995_);
v___x_2002_ = v___x_1991_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_1995_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_u_1997_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_cachedPUnit_1999_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v_cachedPUnitUnit_2000_);
v___x_2002_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2002_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2006_ = 0;
v___x_2007_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2005_, v___x_2006_, v_a_1980_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___y_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
if (v_hasContinue_1979_ == 0)
{
v___y_2010_ = v_a_2008_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_2042_ = lean_box(0);
lean_inc(v_u_1997_);
v___x_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_u_1997_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = l_Lean_mkConst(v___x_2041_, v___x_2043_);
v___x_2045_ = l_Lean_Expr_app___override(v___x_2044_, v_a_2008_);
v___y_2010_ = v___x_2045_;
goto v___jp_2009_;
}
v___jp_2009_:
{
lean_object* v___x_2011_; 
lean_inc_ref(v_doBlockResultType_1996_);
v___x_2011_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1996_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1));
v___x_2014_ = lean_box(0);
lean_inc(v_v_1998_);
v___x_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_v_1998_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
lean_inc(v_u_1997_);
v___x_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_u_1997_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_mkConst(v___x_2013_, v___x_2016_);
v___x_2018_ = l_Lean_mkApp3(v___x_2017_, v___y_2010_, v_a_1995_, v_a_2004_);
lean_inc(v_a_1986_);
lean_inc_ref(v_a_1985_);
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc_ref(v_a_1980_);
v___x_2019_ = lean_apply_9(v_runInBase_1989_, v___x_2018_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, lean_box(0));
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_n(v_a_2020_, 2);
lean_dec_ref_known(v___x_2019_, 1);
lean_inc(v_a_1986_);
lean_inc_ref(v_a_1985_);
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
v___x_2021_ = lean_infer_type(v_a_2020_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2));
v___x_2024_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2023_, v_a_2012_, v_a_2022_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v___x_2024_, 0);
lean_dec(v_unused_2032_);
v___x_2026_ = v___x_2024_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_dec(v___x_2024_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_a_2020_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2020_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_2020_);
v_a_2033_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2024_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_dec(v_a_2020_);
lean_dec(v_a_2012_);
return v___x_2021_;
}
}
else
{
lean_dec(v_a_2012_);
return v___x_2019_;
}
}
else
{
lean_dec_ref(v___y_2010_);
lean_dec(v_a_2004_);
lean_dec(v_a_1995_);
lean_dec_ref(v_runInBase_1989_);
return v___x_2011_;
}
}
}
else
{
lean_dec(v_a_2004_);
lean_dec(v_a_1995_);
lean_dec_ref(v_runInBase_1989_);
return v___x_2007_;
}
}
else
{
lean_dec(v_a_1995_);
lean_dec_ref(v_runInBase_1989_);
return v___x_2003_;
}
}
}
else
{
lean_del_object(v___x_1991_);
lean_dec_ref(v_runInBase_1989_);
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object* v_base_2051_, lean_object* v_hasContinue_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
uint8_t v_hasContinue_boxed_2061_; lean_object* v_res_2062_; 
v_hasContinue_boxed_2061_ = lean_unbox(v_hasContinue_2052_);
v_res_2062_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2051_, v_hasContinue_boxed_2061_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object* v_base_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_m_2077_; lean_object* v_runInBase_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2129_; 
v_m_2077_ = lean_ctor_get(v_base_2068_, 1);
v_runInBase_2078_ = lean_ctor_get(v_base_2068_, 3);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_base_2068_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2130_ = lean_ctor_get(v_base_2068_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_base_2068_, 2);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_base_2068_, 0);
lean_dec(v_unused_2132_);
v___x_2080_ = v_base_2068_;
v_isShared_2081_ = v_isSharedCheck_2129_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_runInBase_2078_);
lean_inc(v_m_2077_);
lean_dec(v_base_2068_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2129_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; 
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2070_);
lean_inc_ref(v_a_2069_);
v___x_2082_ = lean_apply_8(v_m_2077_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, lean_box(0));
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_monadInfo_2083_; lean_object* v_a_2084_; lean_object* v_doBlockResultType_2085_; lean_object* v_u_2086_; lean_object* v_v_2087_; lean_object* v_cachedPUnit_2088_; lean_object* v_cachedPUnitUnit_2089_; lean_object* v___x_2091_; 
v_monadInfo_2083_ = lean_ctor_get(v_a_2069_, 0);
v_a_2084_ = lean_ctor_get(v___x_2082_, 0);
lean_inc_n(v_a_2084_, 2);
lean_dec_ref_known(v___x_2082_, 1);
v_doBlockResultType_2085_ = lean_ctor_get(v_a_2069_, 3);
v_u_2086_ = lean_ctor_get(v_monadInfo_2083_, 1);
v_v_2087_ = lean_ctor_get(v_monadInfo_2083_, 2);
v_cachedPUnit_2088_ = lean_ctor_get(v_monadInfo_2083_, 3);
v_cachedPUnitUnit_2089_ = lean_ctor_get(v_monadInfo_2083_, 4);
lean_inc_ref(v_cachedPUnitUnit_2089_);
lean_inc_ref(v_cachedPUnit_2088_);
lean_inc(v_v_2087_);
lean_inc(v_u_2086_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 4, v_cachedPUnitUnit_2089_);
lean_ctor_set(v___x_2080_, 3, v_cachedPUnit_2088_);
lean_ctor_set(v___x_2080_, 2, v_v_2087_);
lean_ctor_set(v___x_2080_, 1, v_u_2086_);
lean_ctor_set(v___x_2080_, 0, v_a_2084_);
v___x_2091_ = v___x_2080_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2084_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_u_2086_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_2087_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_cachedPUnit_2088_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_cachedPUnitUnit_2089_);
v___x_2091_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; 
v___x_2092_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2091_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2095_ = 0;
v___x_2096_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2094_, v___x_2095_, v_a_2069_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
lean_inc_ref(v_doBlockResultType_2085_);
v___x_2098_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2085_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1));
v___x_2101_ = lean_box(0);
lean_inc(v_v_2087_);
v___x_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_v_2087_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
lean_inc(v_u_2086_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_u_2086_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_mkConst(v___x_2100_, v___x_2103_);
v___x_2105_ = l_Lean_mkApp3(v___x_2104_, v_a_2097_, v_a_2084_, v_a_2093_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2070_);
lean_inc_ref(v_a_2069_);
v___x_2106_ = lean_apply_9(v_runInBase_2078_, v___x_2105_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, lean_box(0));
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_n(v_a_2107_, 2);
lean_dec_ref_known(v___x_2106_, 1);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
v___x_2108_ = lean_infer_type(v_a_2107_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2));
v___x_2111_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2110_, v_a_2099_, v_a_2109_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v___x_2111_, 0);
lean_dec(v_unused_2119_);
v___x_2113_ = v___x_2111_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_dec(v___x_2111_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v_a_2107_);
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2107_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2107_);
v_a_2120_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2111_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2111_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v_a_2107_);
lean_dec(v_a_2099_);
return v___x_2108_;
}
}
else
{
lean_dec(v_a_2099_);
return v___x_2106_;
}
}
else
{
lean_dec(v_a_2097_);
lean_dec(v_a_2093_);
lean_dec(v_a_2084_);
lean_dec_ref(v_runInBase_2078_);
return v___x_2098_;
}
}
else
{
lean_dec(v_a_2093_);
lean_dec(v_a_2084_);
lean_dec_ref(v_runInBase_2078_);
return v___x_2096_;
}
}
else
{
lean_dec(v_a_2084_);
lean_dec_ref(v_runInBase_2078_);
return v___x_2092_;
}
}
}
else
{
lean_del_object(v___x_2080_);
lean_dec_ref(v_runInBase_2078_);
return v___x_2082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object* v_base_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object* v_base_2151_, lean_object* v_r_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_m_2161_; lean_object* v_runInBase_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2208_; 
v_m_2161_ = lean_ctor_get(v_base_2151_, 1);
v_runInBase_2162_ = lean_ctor_get(v_base_2151_, 3);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_base_2151_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; 
v_unused_2209_ = lean_ctor_get(v_base_2151_, 4);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_base_2151_, 2);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_base_2151_, 0);
lean_dec(v_unused_2211_);
v___x_2164_ = v_base_2151_;
v_isShared_2165_ = v_isSharedCheck_2208_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_runInBase_2162_);
lean_inc(v_m_2161_);
lean_dec(v_base_2151_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2208_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; 
lean_inc(v_a_2159_);
lean_inc_ref(v_a_2158_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc_ref(v_a_2153_);
v___x_2166_ = lean_apply_8(v_m_2161_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, lean_box(0));
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_monadInfo_2167_; lean_object* v_a_2168_; lean_object* v_doBlockResultType_2169_; lean_object* v_u_2170_; lean_object* v_v_2171_; lean_object* v_cachedPUnit_2172_; lean_object* v_cachedPUnitUnit_2173_; lean_object* v___x_2175_; 
v_monadInfo_2167_ = lean_ctor_get(v_a_2153_, 0);
v_a_2168_ = lean_ctor_get(v___x_2166_, 0);
lean_inc_n(v_a_2168_, 2);
lean_dec_ref_known(v___x_2166_, 1);
v_doBlockResultType_2169_ = lean_ctor_get(v_a_2153_, 3);
v_u_2170_ = lean_ctor_get(v_monadInfo_2167_, 1);
v_v_2171_ = lean_ctor_get(v_monadInfo_2167_, 2);
v_cachedPUnit_2172_ = lean_ctor_get(v_monadInfo_2167_, 3);
v_cachedPUnitUnit_2173_ = lean_ctor_get(v_monadInfo_2167_, 4);
lean_inc_ref(v_cachedPUnitUnit_2173_);
lean_inc_ref(v_cachedPUnit_2172_);
lean_inc(v_v_2171_);
lean_inc(v_u_2170_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 4, v_cachedPUnitUnit_2173_);
lean_ctor_set(v___x_2164_, 3, v_cachedPUnit_2172_);
lean_ctor_set(v___x_2164_, 2, v_v_2171_);
lean_ctor_set(v___x_2164_, 1, v_u_2170_);
lean_ctor_set(v___x_2164_, 0, v_a_2168_);
v___x_2175_ = v___x_2164_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2168_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_u_2170_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_cachedPUnit_2172_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v_cachedPUnitUnit_2173_);
v___x_2175_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2175_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
lean_inc(v_a_2159_);
lean_inc_ref(v_a_2158_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc_ref(v_r_2152_);
v___x_2178_ = lean_infer_type(v_r_2152_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1));
v___x_2181_ = 0;
v___x_2182_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2180_, v___x_2181_, v_a_2153_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
lean_inc_ref(v_doBlockResultType_2169_);
v___x_2184_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2169_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
v___x_2187_ = lean_box(0);
lean_inc(v_v_2171_);
v___x_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_v_2171_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_inc(v_u_2170_);
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_u_2170_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
lean_inc_ref(v___x_2189_);
v___x_2190_ = l_Lean_mkConst(v___x_2186_, v___x_2189_);
lean_inc(v_a_2183_);
lean_inc(v_a_2179_);
v___x_2191_ = l_Lean_mkAppB(v___x_2190_, v_a_2179_, v_a_2183_);
lean_inc(v_a_2168_);
v___x_2192_ = l_Lean_Expr_app___override(v_a_2168_, v___x_2191_);
v___x_2193_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2));
v___x_2194_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2193_, v_a_2185_, v___x_2192_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref_known(v___x_2194_, 1);
v___x_2195_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4));
v___x_2196_ = l_Lean_mkConst(v___x_2195_, v___x_2189_);
v___x_2197_ = l_Lean_mkApp5(v___x_2196_, v_a_2179_, v_a_2168_, v_a_2183_, v_a_2177_, v_r_2152_);
lean_inc(v_a_2159_);
lean_inc_ref(v_a_2158_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc_ref(v_a_2153_);
v___x_2198_ = lean_apply_9(v_runInBase_2162_, v___x_2197_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, lean_box(0));
return v___x_2198_;
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref_known(v___x_2189_, 2);
lean_dec(v_a_2183_);
lean_dec(v_a_2179_);
lean_dec(v_a_2177_);
lean_dec(v_a_2168_);
lean_dec_ref(v_runInBase_2162_);
lean_dec_ref(v_r_2152_);
v_a_2199_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2194_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2194_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_dec(v_a_2183_);
lean_dec(v_a_2179_);
lean_dec(v_a_2177_);
lean_dec(v_a_2168_);
lean_dec_ref(v_runInBase_2162_);
lean_dec_ref(v_r_2152_);
return v___x_2184_;
}
}
else
{
lean_dec(v_a_2179_);
lean_dec(v_a_2177_);
lean_dec(v_a_2168_);
lean_dec_ref(v_runInBase_2162_);
lean_dec_ref(v_r_2152_);
return v___x_2182_;
}
}
else
{
lean_dec(v_a_2177_);
lean_dec(v_a_2168_);
lean_dec_ref(v_runInBase_2162_);
lean_dec_ref(v_r_2152_);
return v___x_2178_;
}
}
else
{
lean_dec(v_a_2168_);
lean_dec_ref(v_runInBase_2162_);
lean_dec_ref(v_r_2152_);
return v___x_2176_;
}
}
}
else
{
lean_del_object(v___x_2164_);
lean_dec_ref(v_runInBase_2162_);
lean_dec_ref(v_r_2152_);
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object* v_base_2212_, lean_object* v_r_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2212_, v_r_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec_ref(v_a_2214_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object* v_base_2237_, lean_object* v_resultName_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_m_2247_; lean_object* v_runInBase_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2281_; 
v_m_2247_ = lean_ctor_get(v_base_2237_, 1);
v_runInBase_2248_ = lean_ctor_get(v_base_2237_, 3);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_base_2237_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; lean_object* v_unused_2283_; lean_object* v_unused_2284_; 
v_unused_2282_ = lean_ctor_get(v_base_2237_, 4);
lean_dec(v_unused_2282_);
v_unused_2283_ = lean_ctor_get(v_base_2237_, 2);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v_base_2237_, 0);
lean_dec(v_unused_2284_);
v___x_2250_ = v_base_2237_;
v_isShared_2251_ = v_isSharedCheck_2281_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_runInBase_2248_);
lean_inc(v_m_2247_);
lean_dec(v_base_2237_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2281_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; 
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_a_2240_);
lean_inc_ref(v_a_2239_);
v___x_2252_ = lean_apply_8(v_m_2247_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, lean_box(0));
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_monadInfo_2253_; lean_object* v_a_2254_; lean_object* v_u_2255_; lean_object* v_v_2256_; lean_object* v_cachedPUnit_2257_; lean_object* v_cachedPUnitUnit_2258_; lean_object* v___x_2260_; 
v_monadInfo_2253_ = lean_ctor_get(v_a_2239_, 0);
v_a_2254_ = lean_ctor_get(v___x_2252_, 0);
lean_inc_n(v_a_2254_, 2);
lean_dec_ref_known(v___x_2252_, 1);
v_u_2255_ = lean_ctor_get(v_monadInfo_2253_, 1);
v_v_2256_ = lean_ctor_get(v_monadInfo_2253_, 2);
v_cachedPUnit_2257_ = lean_ctor_get(v_monadInfo_2253_, 3);
v_cachedPUnitUnit_2258_ = lean_ctor_get(v_monadInfo_2253_, 4);
lean_inc_ref(v_cachedPUnitUnit_2258_);
lean_inc_ref(v_cachedPUnit_2257_);
lean_inc(v_v_2256_);
lean_inc(v_u_2255_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 4, v_cachedPUnitUnit_2258_);
lean_ctor_set(v___x_2250_, 3, v_cachedPUnit_2257_);
lean_ctor_set(v___x_2250_, 2, v_v_2256_);
lean_ctor_set(v___x_2250_, 1, v_u_2255_);
lean_ctor_set(v___x_2250_, 0, v_a_2254_);
v___x_2260_ = v___x_2250_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2254_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_u_2255_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_v_2256_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_cachedPUnit_2257_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_cachedPUnitUnit_2258_);
v___x_2260_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2260_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = l_Lean_Meta_getFVarFromUserName(v_resultName_2238_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_n(v_a_2264_, 2);
lean_dec_ref_known(v___x_2263_, 1);
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
v___x_2265_ = lean_infer_type(v_a_2264_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__2));
v___x_2268_ = lean_box(0);
lean_inc(v_v_2256_);
v___x_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_v_2256_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
lean_inc(v_u_2255_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v_u_2255_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
lean_inc_ref_n(v___x_2270_, 2);
v___x_2271_ = l_Lean_mkConst(v___x_2267_, v___x_2270_);
v___x_2272_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__4));
v___x_2273_ = l_Lean_mkConst(v___x_2272_, v___x_2270_);
lean_inc_n(v_a_2254_, 2);
v___x_2274_ = l_Lean_mkAppB(v___x_2273_, v_a_2254_, v_a_2262_);
v___x_2275_ = l_Lean_mkAppB(v___x_2271_, v_a_2254_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__7));
v___x_2277_ = l_Lean_mkConst(v___x_2276_, v___x_2270_);
v___x_2278_ = l_Lean_mkApp4(v___x_2277_, v_a_2254_, v___x_2275_, v_a_2266_, v_a_2264_);
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_a_2240_);
lean_inc_ref(v_a_2239_);
v___x_2279_ = lean_apply_9(v_runInBase_2248_, v___x_2278_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, lean_box(0));
return v___x_2279_;
}
else
{
lean_dec(v_a_2264_);
lean_dec(v_a_2262_);
lean_dec(v_a_2254_);
lean_dec_ref(v_runInBase_2248_);
return v___x_2265_;
}
}
else
{
lean_dec(v_a_2262_);
lean_dec(v_a_2254_);
lean_dec_ref(v_runInBase_2248_);
return v___x_2263_;
}
}
else
{
lean_dec(v_a_2254_);
lean_dec_ref(v_runInBase_2248_);
lean_dec(v_resultName_2238_);
return v___x_2261_;
}
}
}
else
{
lean_del_object(v___x_2250_);
lean_dec_ref(v_runInBase_2248_);
lean_dec(v_resultName_2238_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object* v_base_2285_, lean_object* v_resultName_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2285_, v_resultName_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec_ref(v_a_2287_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(lean_object* v_info_2296_, lean_object* v_as_2297_, size_t v_i_2298_, size_t v_stop_2299_, lean_object* v_b_2300_){
_start:
{
lean_object* v___y_2302_; uint8_t v___x_2306_; 
v___x_2306_ = lean_usize_dec_eq(v_i_2298_, v_stop_2299_);
if (v___x_2306_ == 0)
{
lean_object* v_reassigns_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_reassigns_2307_ = lean_ctor_get(v_info_2296_, 1);
v___x_2308_ = lean_array_uget_borrowed(v_as_2297_, v_i_2298_);
v___x_2309_ = l_Lean_Elab_Do_MutVar_getId(v___x_2308_);
v___x_2310_ = l_Lean_NameSet_contains(v_reassigns_2307_, v___x_2309_);
lean_dec(v___x_2309_);
if (v___x_2310_ == 0)
{
v___y_2302_ = v_b_2300_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2311_; 
lean_inc(v___x_2308_);
v___x_2311_ = lean_array_push(v_b_2300_, v___x_2308_);
v___y_2302_ = v___x_2311_;
goto v___jp_2301_;
}
}
else
{
return v_b_2300_;
}
v___jp_2301_:
{
size_t v___x_2303_; size_t v___x_2304_; 
v___x_2303_ = ((size_t)1ULL);
v___x_2304_ = lean_usize_add(v_i_2298_, v___x_2303_);
v_i_2298_ = v___x_2304_;
v_b_2300_ = v___y_2302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0___boxed(lean_object* v_info_2312_, lean_object* v_as_2313_, lean_object* v_i_2314_, lean_object* v_stop_2315_, lean_object* v_b_2316_){
_start:
{
size_t v_i_boxed_2317_; size_t v_stop_boxed_2318_; lean_object* v_res_2319_; 
v_i_boxed_2317_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_stop_boxed_2318_ = lean_unbox_usize(v_stop_2315_);
lean_dec(v_stop_2315_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2312_, v_as_2313_, v_i_boxed_2317_, v_stop_boxed_2318_, v_b_2316_);
lean_dec_ref(v_as_2313_);
lean_dec_ref(v_info_2312_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object* v_info_2322_, lean_object* v_dec_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v_continueBase_x3f_2335_; lean_object* v_controlStack_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v_monadInfo_2364_; lean_object* v_mutVars_2365_; uint8_t v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v_breakBase_x3f_2370_; lean_object* v_controlStack_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; uint8_t v___y_2382_; uint8_t v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v_controlStack_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2397_; uint8_t v___y_2398_; uint8_t v___y_2399_; lean_object* v___y_2400_; lean_object* v_returnBase_x3f_2401_; lean_object* v_controlStack_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2415_; uint8_t v___y_2416_; uint8_t v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2431_; uint8_t v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; uint8_t v___y_2435_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2476_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v_monadInfo_2364_ = lean_ctor_get(v_a_2324_, 0);
v_mutVars_2365_ = lean_ctor_get(v_a_2324_, 1);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v_mutVars_2365_);
v___x_2519_ = ((lean_object*)(l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0));
v___x_2520_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2520_ == 0)
{
v___y_2476_ = v___x_2519_;
goto v___jp_2475_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_nat_dec_le(v___x_2518_, v___x_2518_);
if (v___x_2521_ == 0)
{
if (v___x_2520_ == 0)
{
v___y_2476_ = v___x_2519_;
goto v___jp_2475_;
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2518_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2322_, v_mutVars_2365_, v___x_2522_, v___x_2523_, v___x_2519_);
v___y_2476_ = v___x_2524_;
goto v___jp_2475_;
}
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2518_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2322_, v_mutVars_2365_, v___x_2525_, v___x_2526_, v___x_2519_);
v___y_2476_ = v___x_2527_;
goto v___jp_2475_;
}
}
v___jp_2332_:
{
lean_object* v_stM_2344_; lean_object* v_resultType_2345_; lean_object* v___x_2346_; 
v_stM_2344_ = lean_ctor_get(v_controlStack_2336_, 2);
v_resultType_2345_ = lean_ctor_get(v_dec_2323_, 1);
lean_inc_ref(v_stM_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v___y_2342_);
lean_inc(v___y_2341_);
lean_inc_ref(v___y_2340_);
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc_ref(v_resultType_2345_);
v___x_2346_ = lean_apply_9(v_stM_2344_, v_resultType_2345_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, lean_box(0));
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2355_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2351_, 0, v_dec_2323_);
lean_ctor_set(v___x_2351_, 1, v___y_2334_);
lean_ctor_set(v___x_2351_, 2, v___y_2333_);
lean_ctor_set(v___x_2351_, 3, v_continueBase_x3f_2335_);
lean_ctor_set(v___x_2351_, 4, v_controlStack_2336_);
lean_ctor_set(v___x_2351_, 5, v_a_2347_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2351_);
v___x_2353_ = v___x_2349_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v_controlStack_2336_);
lean_dec(v_continueBase_x3f_2335_);
lean_dec(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v_dec_2323_);
v_a_2356_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2346_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2346_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
v___jp_2366_:
{
if (v___y_2367_ == 0)
{
v___y_2333_ = v_breakBase_x3f_2370_;
v___y_2334_ = v___y_2368_;
v_continueBase_x3f_2335_ = v___y_2369_;
v_controlStack_2336_ = v_controlStack_2371_;
v___y_2337_ = v___y_2372_;
v___y_2338_ = v___y_2373_;
v___y_2339_ = v___y_2374_;
v___y_2340_ = v___y_2375_;
v___y_2341_ = v___y_2376_;
v___y_2342_ = v___y_2377_;
v___y_2343_ = v___y_2378_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v___y_2369_);
lean_inc_ref(v_controlStack_2371_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_controlStack_2371_);
lean_inc_ref(v_monadInfo_2364_);
v___x_2380_ = l_Lean_Elab_Do_ControlStack_continueT(v_monadInfo_2364_, v_controlStack_2371_);
v___y_2333_ = v_breakBase_x3f_2370_;
v___y_2334_ = v___y_2368_;
v_continueBase_x3f_2335_ = v___x_2379_;
v_controlStack_2336_ = v___x_2380_;
v___y_2337_ = v___y_2372_;
v___y_2338_ = v___y_2373_;
v___y_2339_ = v___y_2374_;
v___y_2340_ = v___y_2375_;
v___y_2341_ = v___y_2376_;
v___y_2342_ = v___y_2377_;
v___y_2343_ = v___y_2378_;
goto v___jp_2332_;
}
}
v___jp_2381_:
{
if (v___y_2382_ == 0)
{
lean_inc(v___y_2385_);
v___y_2367_ = v___y_2383_;
v___y_2368_ = v___y_2384_;
v___y_2369_ = v___y_2385_;
v_breakBase_x3f_2370_ = v___y_2385_;
v_controlStack_2371_ = v_controlStack_2386_;
v___y_2372_ = v___y_2387_;
v___y_2373_ = v___y_2388_;
v___y_2374_ = v___y_2389_;
v___y_2375_ = v___y_2390_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2392_;
v___y_2378_ = v___y_2393_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_inc_ref(v_controlStack_2386_);
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_controlStack_2386_);
lean_inc_ref(v_monadInfo_2364_);
v___x_2395_ = l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_2364_, v_controlStack_2386_);
v___y_2367_ = v___y_2383_;
v___y_2368_ = v___y_2384_;
v___y_2369_ = v___y_2385_;
v_breakBase_x3f_2370_ = v___x_2394_;
v_controlStack_2371_ = v___x_2395_;
v___y_2372_ = v___y_2387_;
v___y_2373_ = v___y_2388_;
v___y_2374_ = v___y_2389_;
v___y_2375_ = v___y_2390_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2392_;
v___y_2378_ = v___y_2393_;
goto v___jp_2366_;
}
}
v___jp_2396_:
{
if (lean_obj_tag(v___y_2397_) == 1)
{
lean_object* v_val_2410_; lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v___x_2413_; 
v_val_2410_ = lean_ctor_get(v___y_2397_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v___y_2397_, 1);
v_fst_2411_ = lean_ctor_get(v_val_2410_, 0);
lean_inc(v_fst_2411_);
v_snd_2412_ = lean_ctor_get(v_val_2410_, 1);
lean_inc(v_snd_2412_);
lean_dec(v_val_2410_);
lean_inc_ref(v_monadInfo_2364_);
v___x_2413_ = l_Lean_Elab_Do_ControlStack_stateT(v_monadInfo_2364_, v_fst_2411_, v_snd_2412_, v_controlStack_2402_);
v___y_2382_ = v___y_2398_;
v___y_2383_ = v___y_2399_;
v___y_2384_ = v_returnBase_x3f_2401_;
v___y_2385_ = v___y_2400_;
v_controlStack_2386_ = v___x_2413_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v___y_2404_;
v___y_2389_ = v___y_2405_;
v___y_2390_ = v___y_2406_;
v___y_2391_ = v___y_2407_;
v___y_2392_ = v___y_2408_;
v___y_2393_ = v___y_2409_;
goto v___jp_2381_;
}
else
{
lean_dec(v___y_2397_);
v___y_2382_ = v___y_2398_;
v___y_2383_ = v___y_2399_;
v___y_2384_ = v_returnBase_x3f_2401_;
v___y_2385_ = v___y_2400_;
v_controlStack_2386_ = v_controlStack_2402_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v___y_2404_;
v___y_2389_ = v___y_2405_;
v___y_2390_ = v___y_2406_;
v___y_2391_ = v___y_2407_;
v___y_2392_ = v___y_2408_;
v___y_2393_ = v___y_2409_;
goto v___jp_2381_;
}
}
v___jp_2414_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_box(0);
lean_inc_ref(v_monadInfo_2364_);
v___x_2420_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_2364_);
if (lean_obj_tag(v___y_2415_) == 1)
{
lean_object* v_val_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_val_2421_ = lean_ctor_get(v___y_2415_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___y_2415_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v___y_2415_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_val_2421_);
lean_dec(v___y_2415_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
lean_inc_ref(v___x_2420_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2420_);
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2420_);
v___x_2426_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; 
lean_inc_ref(v_monadInfo_2364_);
v___x_2427_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(v_monadInfo_2364_, v_val_2421_, v___x_2420_);
v___y_2397_ = v___y_2418_;
v___y_2398_ = v___y_2416_;
v___y_2399_ = v___y_2417_;
v___y_2400_ = v___x_2419_;
v_returnBase_x3f_2401_ = v___x_2426_;
v_controlStack_2402_ = v___x_2427_;
v___y_2403_ = v_a_2324_;
v___y_2404_ = v_a_2325_;
v___y_2405_ = v_a_2326_;
v___y_2406_ = v_a_2327_;
v___y_2407_ = v_a_2328_;
v___y_2408_ = v_a_2329_;
v___y_2409_ = v_a_2330_;
goto v___jp_2396_;
}
}
}
else
{
lean_dec(v___y_2415_);
v___y_2397_ = v___y_2418_;
v___y_2398_ = v___y_2416_;
v___y_2399_ = v___y_2417_;
v___y_2400_ = v___x_2419_;
v_returnBase_x3f_2401_ = v___x_2419_;
v_controlStack_2402_ = v___x_2420_;
v___y_2403_ = v_a_2324_;
v___y_2404_ = v_a_2325_;
v___y_2405_ = v_a_2326_;
v___y_2406_ = v_a_2327_;
v___y_2407_ = v_a_2328_;
v___y_2408_ = v_a_2329_;
v___y_2409_ = v_a_2330_;
goto v___jp_2396_;
}
}
v___jp_2430_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2436_ = lean_array_get_size(v___y_2434_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_nat_dec_eq(v___x_2436_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2434_);
lean_ctor_set(v___x_2439_, 1, v___y_2433_);
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
v___y_2415_ = v___y_2431_;
v___y_2416_ = v___y_2432_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___x_2440_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2441_; 
lean_dec_ref(v___y_2434_);
lean_dec_ref(v___y_2433_);
v___x_2441_ = lean_box(0);
v___y_2415_ = v___y_2431_;
v___y_2416_ = v___y_2432_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___x_2441_;
goto v___jp_2414_;
}
}
v___jp_2442_:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2324_);
if (lean_obj_tag(v___x_2447_) == 0)
{
uint8_t v_continues_2448_; 
v_continues_2448_ = lean_ctor_get_uint8(v_info_2322_, sizeof(void*)*2 + 1);
if (v_continues_2448_ == 0)
{
lean_dec_ref_known(v___x_2447_, 1);
v___y_2431_ = v___y_2443_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___y_2445_;
v___y_2435_ = v_continues_2448_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2449_; 
v_a_2449_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2447_, 1);
if (lean_obj_tag(v_a_2449_) == 0)
{
uint8_t v___x_2450_; 
v___x_2450_ = 0;
v___y_2431_ = v___y_2443_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___y_2445_;
v___y_2435_ = v___x_2450_;
goto v___jp_2430_;
}
else
{
lean_dec_ref_known(v_a_2449_, 1);
v___y_2431_ = v___y_2443_;
v___y_2432_ = v___y_2446_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___y_2445_;
v___y_2435_ = v_continues_2448_;
goto v___jp_2430_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v_dec_2323_);
v_a_2451_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2447_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2447_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
v___jp_2459_:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2324_);
if (lean_obj_tag(v___x_2463_) == 0)
{
uint8_t v_breaks_2464_; 
v_breaks_2464_ = lean_ctor_get_uint8(v_info_2322_, sizeof(void*)*2);
if (v_breaks_2464_ == 0)
{
lean_dec_ref_known(v___x_2463_, 1);
v___y_2443_ = v___y_2462_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2461_;
v___y_2446_ = v_breaks_2464_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2465_; 
v_a_2465_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2463_, 1);
if (lean_obj_tag(v_a_2465_) == 0)
{
uint8_t v___x_2466_; 
v___x_2466_ = 0;
v___y_2443_ = v___y_2462_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2461_;
v___y_2446_ = v___x_2466_;
goto v___jp_2442_;
}
else
{
lean_dec_ref_known(v_a_2465_, 1);
v___y_2443_ = v___y_2462_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2461_;
v___y_2446_ = v_breaks_2464_;
goto v___jp_2442_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v_dec_2323_);
v_a_2467_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2463_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2463_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
v___jp_2475_:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2324_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; size_t v_sz_2479_; size_t v___x_2480_; lean_object* v___x_2481_; size_t v_sz_2482_; lean_object* v___x_2483_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v_sz_2479_ = lean_array_size(v___y_2476_);
v___x_2480_ = ((size_t)0ULL);
lean_inc_ref(v___y_2476_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_2479_, v___x_2480_, v___y_2476_);
v_sz_2482_ = lean_array_size(v___x_2481_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_2482_, v___x_2480_, v___x_2481_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v_u_2485_; lean_object* v___x_2486_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_u_2485_ = lean_ctor_get(v_monadInfo_2364_, 1);
lean_inc(v_u_2485_);
v___x_2486_ = l_Lean_Meta_mkProdN(v_a_2484_, v_u_2485_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2486_) == 0)
{
uint8_t v_returnsEarly_2487_; 
v_returnsEarly_2487_ = lean_ctor_get_uint8(v_info_2322_, sizeof(void*)*2 + 2);
if (v_returnsEarly_2487_ == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; 
lean_dec(v_a_2478_);
v_a_2488_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2489_ = lean_box(0);
v___y_2460_ = v_a_2488_;
v___y_2461_ = v___y_2476_;
v___y_2462_ = v___x_2489_;
goto v___jp_2459_;
}
else
{
lean_object* v_a_2490_; lean_object* v_resultType_2491_; lean_object* v___x_2492_; 
v_a_2490_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2486_, 1);
v_resultType_2491_ = lean_ctor_get(v_a_2478_, 0);
lean_inc_ref(v_resultType_2491_);
lean_dec(v_a_2478_);
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_resultType_2491_);
v___y_2460_ = v_a_2490_;
v___y_2461_ = v___y_2476_;
v___y_2462_ = v___x_2492_;
goto v___jp_2459_;
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_a_2478_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_dec_2323_);
v_a_2493_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2486_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2486_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_a_2478_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_dec_2323_);
v_a_2501_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2483_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2483_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_dec_2323_);
v_a_2509_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2477_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2477_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___boxed(lean_object* v_info_2528_, lean_object* v_dec_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_info_2528_, v_dec_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v_a_2530_);
lean_dec_ref(v_info_2528_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object* v_l_2539_, lean_object* v_elabElem_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2541_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2541_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2541_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2599_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
if (lean_obj_tag(v_a_2550_) == 1)
{
lean_object* v_breakBase_x3f_2610_; 
v_breakBase_x3f_2610_ = lean_ctor_get(v_l_2539_, 2);
lean_inc(v_breakBase_x3f_2610_);
if (lean_obj_tag(v_breakBase_x3f_2610_) == 1)
{
lean_object* v_continueBase_x3f_2611_; lean_object* v_val_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref_known(v_a_2550_, 1);
v_continueBase_x3f_2611_ = lean_ctor_get(v_l_2539_, 3);
v_val_2612_ = lean_ctor_get(v_breakBase_x3f_2610_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_breakBase_x3f_2610_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2614_ = v_breakBase_x3f_2610_;
v_isShared_2615_ = v_isSharedCheck_2625_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_val_2612_);
lean_dec(v_breakBase_x3f_2610_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2625_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___y_2617_; 
if (lean_obj_tag(v_continueBase_x3f_2611_) == 0)
{
uint8_t v___x_2623_; 
v___x_2623_ = 0;
v___y_2617_ = v___x_2623_;
goto v___jp_2616_;
}
else
{
uint8_t v___x_2624_; 
v___x_2624_ = 1;
v___y_2617_ = v___x_2624_;
goto v___jp_2616_;
}
v___jp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = lean_box(v___y_2617_);
v___x_2619_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkBreak___boxed), 10, 2);
lean_closure_set(v___x_2619_, 0, v_val_2612_);
lean_closure_set(v___x_2619_, 1, v___x_2618_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2619_);
v___x_2621_ = v___x_2614_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
v___y_2599_ = v___x_2621_;
goto v___jp_2598_;
}
}
}
}
else
{
lean_dec(v_breakBase_x3f_2610_);
v___y_2599_ = v_a_2550_;
goto v___jp_2598_;
}
}
else
{
v___y_2599_ = v_a_2550_;
goto v___jp_2598_;
}
v___jp_2555_:
{
lean_object* v_origCont_2559_; lean_object* v_liftedStack_2560_; lean_object* v_liftedDoBlockResultType_2561_; lean_object* v_resultName_2562_; lean_object* v_resultType_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2581_; 
v_origCont_2559_ = lean_ctor_get(v_l_2539_, 0);
lean_inc_ref(v_origCont_2559_);
v_liftedStack_2560_ = lean_ctor_get(v_l_2539_, 4);
lean_inc_ref(v_liftedStack_2560_);
v_liftedDoBlockResultType_2561_ = lean_ctor_get(v_l_2539_, 5);
lean_inc_ref(v_liftedDoBlockResultType_2561_);
lean_dec_ref(v_l_2539_);
v_resultName_2562_ = lean_ctor_get(v_origCont_2559_, 0);
v_resultType_2563_ = lean_ctor_get(v_origCont_2559_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_origCont_2559_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v_origCont_2559_, 2);
lean_dec(v_unused_2582_);
v___x_2565_ = v_origCont_2559_;
v_isShared_2566_ = v_isSharedCheck_2581_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_resultType_2563_);
lean_inc(v_resultName_2562_);
lean_dec(v_origCont_2559_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2581_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_monadInfo_2567_; lean_object* v_mutVars_2568_; lean_object* v_mutVarDefs_2569_; uint8_t v_deadCode_2570_; lean_object* v_ops_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; lean_object* v___x_2577_; 
v_monadInfo_2567_ = lean_ctor_get(v_a_2541_, 0);
v_mutVars_2568_ = lean_ctor_get(v_a_2541_, 1);
v_mutVarDefs_2569_ = lean_ctor_get(v_a_2541_, 2);
v_deadCode_2570_ = lean_ctor_get_uint8(v_a_2541_, sizeof(void*)*6);
v_ops_2571_ = lean_ctor_get(v_a_2541_, 5);
lean_inc(v_resultName_2562_);
v___x_2572_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkPure___boxed), 10, 2);
lean_closure_set(v___x_2572_, 0, v_liftedStack_2560_);
lean_closure_set(v___x_2572_, 1, v_resultName_2562_);
v___x_2573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2558_);
lean_ctor_set(v___x_2573_, 1, v___y_2556_);
lean_ctor_set(v___x_2573_, 2, v___y_2557_);
v___x_2574_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_2573_);
lean_dec_ref_known(v___x_2573_, 3);
v___x_2575_ = 1;
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 2, v___x_2572_);
v___x_2577_ = v___x_2565_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_resultName_2562_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_resultType_2563_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v___x_2572_);
v___x_2577_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*3, v___x_2575_);
lean_inc(v_ops_2571_);
lean_inc_ref(v_mutVarDefs_2569_);
lean_inc_ref(v_mutVars_2568_);
lean_inc_ref(v_monadInfo_2567_);
v___x_2578_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2578_, 0, v_monadInfo_2567_);
lean_ctor_set(v___x_2578_, 1, v_mutVars_2568_);
lean_ctor_set(v___x_2578_, 2, v_mutVarDefs_2569_);
lean_ctor_set(v___x_2578_, 3, v_liftedDoBlockResultType_2561_);
lean_ctor_set(v___x_2578_, 4, v___x_2574_);
lean_ctor_set(v___x_2578_, 5, v_ops_2571_);
lean_ctor_set_uint8(v___x_2578_, sizeof(void*)*6, v_deadCode_2570_);
lean_inc(v_a_2547_);
lean_inc_ref(v_a_2546_);
lean_inc(v_a_2545_);
lean_inc_ref(v_a_2544_);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
v___x_2579_ = lean_apply_9(v_elabElem_2540_, v___x_2577_, v___x_2578_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, lean_box(0));
return v___x_2579_;
}
}
}
v___jp_2583_:
{
lean_object* v_returnBase_x3f_2586_; 
v_returnBase_x3f_2586_ = lean_ctor_get(v_l_2539_, 1);
if (lean_obj_tag(v_returnBase_x3f_2586_) == 1)
{
lean_object* v_val_2587_; lean_object* v_resultType_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2596_; 
v_val_2587_ = lean_ctor_get(v_returnBase_x3f_2586_, 0);
v_resultType_2588_ = lean_ctor_get(v_a_2554_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_a_2554_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v_a_2554_, 1);
lean_dec(v_unused_2597_);
v___x_2590_ = v_a_2554_;
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_resultType_2588_);
lean_dec(v_a_2554_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2596_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_inc(v_val_2587_);
v___x_2592_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkReturn___boxed), 10, 1);
lean_closure_set(v___x_2592_, 0, v_val_2587_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 1, v___x_2592_);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_resultType_2588_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v___x_2594_;
goto v___jp_2555_;
}
}
}
else
{
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v_a_2554_;
goto v___jp_2555_;
}
}
v___jp_2598_:
{
if (lean_obj_tag(v_a_2552_) == 1)
{
lean_object* v_continueBase_x3f_2600_; 
v_continueBase_x3f_2600_ = lean_ctor_get(v_l_2539_, 3);
lean_inc(v_continueBase_x3f_2600_);
if (lean_obj_tag(v_continueBase_x3f_2600_) == 1)
{
lean_object* v_val_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref_known(v_a_2552_, 1);
v_val_2601_ = lean_ctor_get(v_continueBase_x3f_2600_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_continueBase_x3f_2600_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2603_ = v_continueBase_x3f_2600_;
v_isShared_2604_ = v_isSharedCheck_2609_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_val_2601_);
lean_dec(v_continueBase_x3f_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2609_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkContinue___boxed), 9, 1);
lean_closure_set(v___x_2605_, 0, v_val_2601_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
v___y_2584_ = v___y_2599_;
v___y_2585_ = v___x_2607_;
goto v___jp_2583_;
}
}
}
else
{
lean_dec(v_continueBase_x3f_2600_);
v___y_2584_ = v___y_2599_;
v___y_2585_ = v_a_2552_;
goto v___jp_2583_;
}
}
else
{
v___y_2584_ = v___y_2599_;
v___y_2585_ = v_a_2552_;
goto v___jp_2583_;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_a_2552_);
lean_dec(v_a_2550_);
lean_dec_ref(v_elabElem_2540_);
lean_dec_ref(v_l_2539_);
v_a_2626_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2553_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2553_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_elabElem_2540_);
lean_dec_ref(v_l_2539_);
v_a_2634_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2551_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2551_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec_ref(v_elabElem_2540_);
lean_dec_ref(v_l_2539_);
v_a_2642_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2549_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2549_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift___boxed(lean_object* v_l_2650_, lean_object* v_elabElem_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Elab_Do_EffectForwarder_lift(v_l_2650_, v_elabElem_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object* v_l_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_liftedStack_2670_; lean_object* v_origCont_2671_; lean_object* v_restoreCont_2672_; lean_object* v___x_2673_; 
v_liftedStack_2670_ = lean_ctor_get(v_l_2661_, 4);
lean_inc_ref(v_liftedStack_2670_);
v_origCont_2671_ = lean_ctor_get(v_l_2661_, 0);
lean_inc_ref(v_origCont_2671_);
lean_dec_ref(v_l_2661_);
v_restoreCont_2672_ = lean_ctor_get(v_liftedStack_2670_, 4);
lean_inc_ref(v_restoreCont_2672_);
lean_dec_ref(v_liftedStack_2670_);
lean_inc(v_a_2668_);
lean_inc_ref(v_a_2667_);
lean_inc(v_a_2666_);
lean_inc_ref(v_a_2665_);
lean_inc(v_a_2664_);
lean_inc_ref(v_a_2663_);
lean_inc_ref(v_a_2662_);
v___x_2673_ = lean_apply_9(v_restoreCont_2672_, v_origCont_2671_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, lean_box(0));
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont___boxed(lean_object* v_l_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_l_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec_ref(v_a_2675_);
return v_res_2683_;
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
