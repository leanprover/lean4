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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__2));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__4));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__6));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM(lean_object* v_m_59_, lean_object* v_stM_u03b1_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_70_ = 0;
v___x_71_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_69_, v___x_70_, v_a_61_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v_stM_73_; lean_object* v___x_74_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_n(v_a_72_, 2);
lean_dec_ref_known(v___x_71_, 1);
v_stM_73_ = lean_ctor_get(v_m_59_, 2);
lean_inc_ref(v_stM_73_);
lean_dec_ref(v_m_59_);
lean_inc(v_a_67_);
lean_inc_ref(v_a_66_);
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc_ref(v_a_61_);
v___x_74_ = lean_apply_9(v_stM_73_, v_a_72_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, lean_box(0));
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc_n(v_a_75_, 2);
lean_dec_ref_known(v___x_74_, 1);
lean_inc_ref(v_stM_u03b1_60_);
v___x_76_ = l_Lean_Meta_isExprDefEq(v_stM_u03b1_60_, v_a_75_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_103_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_103_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_103_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_103_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = lean_unbox(v_a_77_);
lean_dec(v_a_77_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_del_object(v___x_79_);
lean_dec(v_a_72_);
v___x_82_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__3, &l_Lean_Elab_Do_ControlStack_unStM___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3);
v___x_83_ = l_Lean_MessageData_ofExpr(v_stM_u03b1_60_);
v___x_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__5, &l_Lean_Elab_Do_ControlStack_unStM___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5);
v___x_86_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Lean_MessageData_ofExpr(v_a_75_);
v___x_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_unStM___closed__7, &l_Lean_Elab_Do_ControlStack_unStM___closed__7_once, _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7);
v___x_90_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_90_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
lean_object* v___x_101_; 
lean_dec(v_a_75_);
lean_dec_ref(v_stM_u03b1_60_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v_a_72_);
v___x_101_ = v___x_79_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_72_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_a_75_);
lean_dec(v_a_72_);
lean_dec_ref(v_stM_u03b1_60_);
v_a_104_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_76_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_76_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
else
{
lean_dec(v_a_72_);
lean_dec_ref(v_stM_u03b1_60_);
return v___x_74_;
}
}
else
{
lean_dec_ref(v_stM_u03b1_60_);
lean_dec_ref(v_m_59_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_unStM___boxed(lean_object* v_m_112_, lean_object* v_stM_u03b1_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Elab_Do_ControlStack_unStM(v_m_112_, v_stM_u03b1_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(lean_object* v_00_u03b1_123_, lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v_msg_124_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___boxed(lean_object* v_00_u03b1_134_, lean_object* v_msg_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(v_00_u03b1_134_, v_msg_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0(lean_object* v_dec_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v_dec_145_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__0___boxed(lean_object* v_dec_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_Do_ControlStack_base___lam__0(v_dec_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1(lean_object* v_00_u03b1_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v_00_u03b1_165_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__1___boxed(lean_object* v_00_u03b1_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Do_ControlStack_base___lam__1(v_00_u03b1_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_184_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1));
v___x_189_ = l_Lean_MessageData_ofFormat(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__2(lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2, &l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once, _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3(lean_object* v_m_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v_m_192_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base___lam__3___boxed(lean_object* v_m_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_Do_ControlStack_base___lam__3(v_m_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_base(lean_object* v_mi_215_){
_start:
{
lean_object* v_m_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_227_; 
v_m_216_ = lean_ctor_get(v_mi_215_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v_mi_215_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_228_ = lean_ctor_get(v_mi_215_, 4);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_mi_215_, 3);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_mi_215_, 2);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_mi_215_, 1);
lean_dec(v_unused_231_);
v___x_218_ = v_mi_215_;
v_isShared_219_ = v_isSharedCheck_227_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_m_216_);
lean_dec(v_mi_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_227_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_225_; 
v___f_220_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__0));
v___f_221_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__1));
v___f_222_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_base___closed__2));
v___f_223_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_base___lam__3___boxed), 9, 1);
lean_closure_set(v___f_223_, 0, v_m_216_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 4, v___f_220_);
lean_ctor_set(v___x_218_, 3, v___f_221_);
lean_ctor_set(v___x_218_, 2, v___f_221_);
lean_ctor_set(v___x_218_, 1, v___f_223_);
lean_ctor_set(v___x_218_, 0, v___f_222_);
v___x_225_ = v___x_218_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___f_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v___f_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(size_t v_sz_232_, size_t v_i_233_, lean_object* v_bs_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = lean_usize_dec_lt(v_i_233_, v_sz_232_);
if (v___x_235_ == 0)
{
return v_bs_234_;
}
else
{
lean_object* v_v_236_; lean_object* v___x_237_; lean_object* v_bs_x27_238_; lean_object* v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
v_v_236_ = lean_array_uget(v_bs_234_, v_i_233_);
v___x_237_ = lean_unsigned_to_nat(0u);
v_bs_x27_238_ = lean_array_uset(v_bs_234_, v_i_233_, v___x_237_);
v___x_239_ = l_Lean_Elab_Do_MutVar_getId(v_v_236_);
lean_dec(v_v_236_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_i_233_, v___x_240_);
v___x_242_ = lean_array_uset(v_bs_x27_238_, v_i_233_, v___x_239_);
v_i_233_ = v___x_241_;
v_bs_234_ = v___x_242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0___boxed(lean_object* v_sz_244_, lean_object* v_i_245_, lean_object* v_bs_246_){
_start:
{
size_t v_sz_boxed_247_; size_t v_i_boxed_248_; lean_object* v_res_249_; 
v_sz_boxed_247_ = lean_unbox_usize(v_sz_244_);
lean_dec(v_sz_244_);
v_i_boxed_248_ = lean_unbox_usize(v_i_245_);
lean_dec(v_i_245_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_boxed_247_, v_i_boxed_248_, v_bs_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(lean_object* v_muts_250_){
_start:
{
size_t v_sz_251_; size_t v___x_252_; lean_object* v___x_253_; 
v_sz_251_ = lean_array_size(v_muts_250_);
v___x_252_ = ((size_t)0ULL);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_251_, v___x_252_, v_muts_250_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(size_t v_sz_254_, size_t v_i_255_, lean_object* v_bs_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = lean_usize_dec_lt(v_i_255_, v_sz_254_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v_bs_256_);
return v___x_263_;
}
else
{
lean_object* v_v_264_; lean_object* v___x_265_; 
v_v_264_ = lean_array_uget_borrowed(v_bs_256_, v_i_255_);
lean_inc(v_v_264_);
v___x_265_ = l_Lean_Meta_getLocalDeclFromUserName(v_v_264_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; lean_object* v_bs_x27_268_; lean_object* v___x_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = lean_unsigned_to_nat(0u);
v_bs_x27_268_ = lean_array_uset(v_bs_256_, v_i_255_, v___x_267_);
v___x_269_ = l_Lean_LocalDecl_type(v_a_266_);
lean_dec(v_a_266_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_add(v_i_255_, v___x_270_);
v___x_272_ = lean_array_uset(v_bs_x27_268_, v_i_255_, v___x_269_);
v_i_255_ = v___x_271_;
v_bs_256_ = v___x_272_;
goto _start;
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_bs_256_);
v_a_274_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_265_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_265_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg___boxed(lean_object* v_sz_282_, lean_object* v_i_283_, lean_object* v_bs_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
size_t v_sz_boxed_290_; size_t v_i_boxed_291_; lean_object* v_res_292_; 
v_sz_boxed_290_ = lean_unbox_usize(v_sz_282_);
lean_dec(v_sz_282_);
v_i_boxed_291_ = lean_unbox_usize(v_i_283_);
lean_dec(v_i_283_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_boxed_290_, v_i_boxed_291_, v_bs_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(lean_object* v_baseMonadInfo_293_, lean_object* v_muts_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; size_t v_sz_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_303_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_muts_294_);
v_sz_304_ = lean_array_size(v___x_303_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_304_, v___x_305_, v___x_303_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_u_308_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v_u_308_ = lean_ctor_get(v_baseMonadInfo_293_, 1);
lean_inc(v_u_308_);
lean_dec_ref(v_baseMonadInfo_293_);
v___x_309_ = l_Lean_Meta_mkProdN(v_a_307_, v_u_308_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
return v___x_309_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v_baseMonadInfo_293_);
v_a_310_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_306_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3___boxed(lean_object* v_baseMonadInfo_318_, lean_object* v_muts_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_318_, v_muts_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec_ref(v_a_320_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(size_t v_sz_329_, size_t v_i_330_, lean_object* v_bs_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_329_, v_i_330_, v_bs_331_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___boxed(lean_object* v_sz_341_, lean_object* v_i_342_, lean_object* v_bs_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
size_t v_sz_boxed_352_; size_t v_i_boxed_353_; lean_object* v_res_354_; 
v_sz_boxed_352_ = lean_unbox_usize(v_sz_341_);
lean_dec(v_sz_341_);
v_i_boxed_353_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(v_sz_boxed_352_, v_i_boxed_353_, v_bs_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(lean_object* v_baseMonadInfo_358_, lean_object* v_muts_359_, lean_object* v_00_u03b1_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
lean_inc_ref(v_baseMonadInfo_358_);
v___x_369_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_358_, v_muts_359_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_384_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_384_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_384_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_384_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_u_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v_u_374_ = lean_ctor_get(v_baseMonadInfo_358_, 1);
lean_inc_n(v_u_374_, 2);
lean_dec_ref(v_baseMonadInfo_358_);
v___x_375_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1));
v___x_376_ = lean_box(0);
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v_u_374_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v_u_374_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = l_Lean_mkConst(v___x_375_, v___x_378_);
v___x_380_ = l_Lean_mkAppB(v___x_379_, v_00_u03b1_360_, v_a_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_380_);
v___x_382_ = v___x_372_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_dec_ref(v_00_u03b1_360_);
lean_dec_ref(v_baseMonadInfo_358_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___boxed(lean_object* v_baseMonadInfo_385_, lean_object* v_muts_386_, lean_object* v_00_u03b1_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_385_, v_muts_386_, v_00_u03b1_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__0(lean_object* v_base_403_, lean_object* v_00_u03c3_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_description_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_description_406_ = lean_ctor_get(v_base_403_, 0);
lean_inc_ref(v_description_406_);
lean_dec_ref(v_base_403_);
v___x_407_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1);
v___x_408_ = l_Lean_MessageData_ofExpr(v_00_u03c3_404_);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_box(0);
v___x_413_ = lean_apply_1(v_description_406_, v___x_412_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_411_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1(lean_object* v_baseMonadInfo_415_, lean_object* v_muts_416_, lean_object* v_base_417_, lean_object* v_00_u03b1_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_415_, v_muts_416_, v_00_u03b1_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_stM_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v_stM_429_ = lean_ctor_get(v_base_417_, 2);
lean_inc_ref(v_stM_429_);
lean_dec_ref(v_base_417_);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
lean_inc_ref(v___y_419_);
v___x_430_ = lean_apply_9(v_stM_429_, v_a_428_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, lean_box(0));
return v___x_430_;
}
else
{
lean_dec_ref(v_base_417_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(lean_object* v_baseMonadInfo_431_, lean_object* v_muts_432_, lean_object* v_base_433_, lean_object* v_00_u03b1_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(v_baseMonadInfo_431_, v_muts_432_, v_base_433_, v_00_u03b1_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2(lean_object* v_a_444_, lean_object* v_muts_445_, lean_object* v_resultName_446_, lean_object* v_k_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_getFVarFromUserName(v_a_444_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_muts_445_);
v___x_459_ = lean_array_to_list(v___x_458_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v_resultName_446_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_Expr_fvarId_x21(v_a_457_);
lean_dec(v_a_457_);
v___x_462_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___x_460_, v___x_461_, v_k_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v___x_462_;
}
else
{
lean_dec_ref(v_k_447_);
lean_dec(v_resultName_446_);
lean_dec_ref(v_muts_445_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed(lean_object* v_a_463_, lean_object* v_muts_464_, lean_object* v_resultName_465_, lean_object* v_k_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_Do_ControlStack_stateT___lam__2(v_a_463_, v_muts_464_, v_resultName_465_, v_k_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3(lean_object* v_baseMonadInfo_479_, lean_object* v_muts_480_, lean_object* v_base_481_, lean_object* v_dec_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1));
v___x_492_ = l_Lean_Core_mkFreshUserName(v___x_491_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v_resultName_494_; lean_object* v_resultType_495_; lean_object* v_k_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_517_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v_resultName_494_ = lean_ctor_get(v_dec_482_, 0);
v_resultType_495_ = lean_ctor_get(v_dec_482_, 1);
v_k_496_ = lean_ctor_get(v_dec_482_, 2);
v_isSharedCheck_517_ = !lean_is_exclusive(v_dec_482_);
if (v_isSharedCheck_517_ == 0)
{
v___x_498_ = v_dec_482_;
v_isShared_499_ = v_isSharedCheck_517_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_k_496_);
lean_inc(v_resultType_495_);
lean_inc(v_resultName_494_);
lean_dec(v_dec_482_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_517_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; 
lean_inc_ref(v_muts_480_);
v___x_500_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_479_, v_muts_480_, v_resultType_495_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_restoreCont_502_; lean_object* v___f_503_; uint8_t v___x_504_; lean_object* v___x_506_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_restoreCont_502_ = lean_ctor_get(v_base_481_, 4);
lean_inc_ref(v_restoreCont_502_);
lean_dec_ref(v_base_481_);
lean_inc(v_a_493_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed), 12, 4);
lean_closure_set(v___f_503_, 0, v_a_493_);
lean_closure_set(v___f_503_, 1, v_muts_480_);
lean_closure_set(v___f_503_, 2, v_resultName_494_);
lean_closure_set(v___f_503_, 3, v_k_496_);
v___x_504_ = 0;
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 2, v___f_503_);
lean_ctor_set(v___x_498_, 1, v_a_501_);
lean_ctor_set(v___x_498_, 0, v_a_493_);
v___x_506_ = v___x_498_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_493_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_a_501_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v___f_503_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*3, v___x_504_);
lean_inc(v___y_489_);
lean_inc_ref(v___y_488_);
lean_inc(v___y_487_);
lean_inc_ref(v___y_486_);
lean_inc(v___y_485_);
lean_inc_ref(v___y_484_);
lean_inc_ref(v___y_483_);
v___x_507_ = lean_apply_9(v_restoreCont_502_, v___x_506_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, lean_box(0));
return v___x_507_;
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_del_object(v___x_498_);
lean_dec_ref(v_k_496_);
lean_dec(v_resultName_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_base_481_);
lean_dec_ref(v_muts_480_);
v_a_509_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_500_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_500_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_dec_482_);
lean_dec_ref(v_base_481_);
lean_dec_ref(v_muts_480_);
lean_dec_ref(v_baseMonadInfo_479_);
v_a_518_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_492_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_492_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(lean_object* v_baseMonadInfo_526_, lean_object* v_muts_527_, lean_object* v_base_528_, lean_object* v_dec_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(v_baseMonadInfo_526_, v_muts_527_, v_base_528_, v_dec_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(size_t v_sz_539_, size_t v_i_540_, lean_object* v_bs_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_lt(v_i_540_, v_sz_539_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_bs_541_);
return v___x_550_;
}
else
{
lean_object* v_v_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_v_551_ = lean_array_uget_borrowed(v_bs_541_, v_i_540_);
v___x_552_ = l_Lean_Elab_Do_MutVar_getId(v_v_551_);
v___x_553_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_552_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v_ident_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v_ident_555_ = lean_ctor_get(v_v_551_, 0);
v___x_556_ = l_Lean_LocalDecl_toExpr(v_a_554_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_box(0);
v___x_559_ = 0;
lean_inc_ref(v___x_556_);
lean_inc(v_ident_555_);
v___x_560_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_555_, v___x_556_, v___x_557_, v___x_557_, v___x_558_, v___x_559_, v___x_559_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; lean_object* v_bs_x27_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
lean_dec_ref_known(v___x_560_, 1);
v___x_561_ = lean_unsigned_to_nat(0u);
v_bs_x27_562_ = lean_array_uset(v_bs_541_, v_i_540_, v___x_561_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_540_, v___x_563_);
v___x_565_ = lean_array_uset(v_bs_x27_562_, v_i_540_, v___x_556_);
v_i_540_ = v___x_564_;
v_bs_541_ = v___x_565_;
goto _start;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v___x_556_);
lean_dec_ref(v_bs_541_);
v_a_567_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_560_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_560_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v_bs_541_);
v_a_575_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_553_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_553_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object* v_sz_583_, lean_object* v_i_584_, lean_object* v_bs_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
size_t v_sz_boxed_593_; size_t v_i_boxed_594_; lean_object* v_res_595_; 
v_sz_boxed_593_ = lean_unbox_usize(v_sz_583_);
lean_dec(v_sz_583_);
v_i_boxed_594_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_593_, v_i_boxed_594_, v_bs_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2));
v___x_601_ = l_Lean_stringToMessageData(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object* v_muts_605_, lean_object* v_baseMonadInfo_606_, lean_object* v_00_u03c3_607_, lean_object* v_base_608_, lean_object* v_e_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
size_t v_sz_618_; size_t v___x_619_; lean_object* v___x_620_; 
v_sz_618_ = lean_array_size(v_muts_605_);
v___x_619_ = ((size_t)0ULL);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_618_, v___x_619_, v_muts_605_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v_u_622_; lean_object* v___x_623_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v_u_622_ = lean_ctor_get(v_baseMonadInfo_606_, 1);
lean_inc(v_u_622_);
lean_dec_ref(v_baseMonadInfo_606_);
v___x_623_ = l_Lean_Meta_mkProdMkN(v_a_621_, v_u_622_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_672_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_fst_625_ = lean_ctor_get(v_a_624_, 0);
v_snd_626_ = lean_ctor_get(v_a_624_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_a_624_);
if (v_isSharedCheck_672_ == 0)
{
v___x_628_ = v_a_624_;
v_isShared_629_ = v_isSharedCheck_672_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_snd_626_);
lean_inc(v_fst_625_);
lean_dec(v_a_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_672_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___x_641_; 
lean_inc_ref(v_00_u03c3_607_);
lean_inc(v_snd_626_);
v___x_641_ = l_Lean_Meta_isExprDefEq(v_snd_626_, v_00_u03c3_607_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; uint8_t v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = lean_unbox(v_a_642_);
lean_dec(v_a_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v_fst_625_);
lean_dec_ref(v_e_609_);
lean_dec_ref(v_base_608_);
v___x_644_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1);
v___x_645_ = l_Lean_MessageData_ofExpr(v_00_u03c3_607_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 7);
lean_ctor_set(v___x_628_, 1, v___x_645_);
lean_ctor_set(v___x_628_, 0, v___x_644_);
v___x_647_ = v___x_628_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_663_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v___x_648_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_MessageData_ofExpr(v_snd_626_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_653_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_del_object(v___x_628_);
lean_dec(v_snd_626_);
lean_dec_ref(v_00_u03c3_607_);
v___y_631_ = v___y_610_;
v___y_632_ = v___y_611_;
v___y_633_ = v___y_612_;
v___y_634_ = v___y_613_;
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
v___y_637_ = v___y_616_;
goto v___jp_630_;
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_del_object(v___x_628_);
lean_dec(v_snd_626_);
lean_dec(v_fst_625_);
lean_dec_ref(v_e_609_);
lean_dec_ref(v_base_608_);
lean_dec_ref(v_00_u03c3_607_);
v_a_664_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_641_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_641_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
v___jp_630_:
{
lean_object* v_runInBase_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_runInBase_638_ = lean_ctor_get(v_base_608_, 3);
lean_inc_ref(v_runInBase_638_);
lean_dec_ref(v_base_608_);
v___x_639_ = l_Lean_Expr_app___override(v_e_609_, v_fst_625_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc_ref(v___y_631_);
v___x_640_ = lean_apply_9(v_runInBase_638_, v___x_639_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, lean_box(0));
return v___x_640_;
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_e_609_);
lean_dec_ref(v_base_608_);
lean_dec_ref(v_00_u03c3_607_);
v_a_673_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_623_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_623_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_e_609_);
lean_dec_ref(v_base_608_);
lean_dec_ref(v_00_u03c3_607_);
lean_dec_ref(v_baseMonadInfo_606_);
v_a_681_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_620_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_620_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object* v_muts_689_, lean_object* v_baseMonadInfo_690_, lean_object* v_00_u03c3_691_, lean_object* v_base_692_, lean_object* v_e_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_muts_689_, v_baseMonadInfo_690_, v_00_u03c3_691_, v_base_692_, v_e_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object* v_baseMonadInfo_706_, lean_object* v_muts_707_, lean_object* v_base_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; 
lean_inc_ref(v_baseMonadInfo_706_);
v___x_717_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_706_, v_muts_707_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_m_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v_m_719_ = lean_ctor_get(v_base_708_, 1);
lean_inc_ref(v_m_719_);
lean_dec_ref(v_base_708_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc(v___y_713_);
lean_inc_ref(v___y_712_);
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc_ref(v___y_709_);
v___x_720_ = lean_apply_8(v_m_719_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, lean_box(0));
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_736_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_736_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_736_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_736_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_u_725_; lean_object* v_v_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v_u_725_ = lean_ctor_get(v_baseMonadInfo_706_, 1);
lean_inc(v_u_725_);
v_v_726_ = lean_ctor_get(v_baseMonadInfo_706_, 2);
lean_inc(v_v_726_);
lean_dec_ref(v_baseMonadInfo_706_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1));
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v_v_726_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v_u_725_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_mkConst(v___x_727_, v___x_730_);
v___x_732_ = l_Lean_mkAppB(v___x_731_, v_a_718_, v_a_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_732_);
v___x_734_ = v___x_723_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_dec(v_a_718_);
lean_dec_ref(v_baseMonadInfo_706_);
return v___x_720_;
}
}
else
{
lean_dec_ref(v_base_708_);
lean_dec_ref(v_baseMonadInfo_706_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object* v_baseMonadInfo_737_, lean_object* v_muts_738_, lean_object* v_base_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_737_, v_muts_738_, v_base_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object* v_baseMonadInfo_749_, lean_object* v_muts_750_, lean_object* v_00_u03c3_751_, lean_object* v_base_752_){
_start:
{
lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
lean_inc_ref(v_00_u03c3_751_);
lean_inc_ref_n(v_base_752_, 4);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0), 3, 2);
lean_closure_set(v___f_753_, 0, v_base_752_);
lean_closure_set(v___f_753_, 1, v_00_u03c3_751_);
lean_inc_ref_n(v_muts_750_, 3);
lean_inc_ref_n(v_baseMonadInfo_749_, 3);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed), 12, 3);
lean_closure_set(v___f_754_, 0, v_baseMonadInfo_749_);
lean_closure_set(v___f_754_, 1, v_muts_750_);
lean_closure_set(v___f_754_, 2, v_base_752_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed), 12, 3);
lean_closure_set(v___f_755_, 0, v_baseMonadInfo_749_);
lean_closure_set(v___f_755_, 1, v_muts_750_);
lean_closure_set(v___f_755_, 2, v_base_752_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed), 13, 4);
lean_closure_set(v___f_756_, 0, v_muts_750_);
lean_closure_set(v___f_756_, 1, v_baseMonadInfo_749_);
lean_closure_set(v___f_756_, 2, v_00_u03c3_751_);
lean_closure_set(v___f_756_, 3, v_base_752_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed), 11, 3);
lean_closure_set(v___f_757_, 0, v_baseMonadInfo_749_);
lean_closure_set(v___f_757_, 1, v_muts_750_);
lean_closure_set(v___f_757_, 2, v_base_752_);
v___x_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_758_, 0, v___f_753_);
lean_ctor_set(v___x_758_, 1, v___f_757_);
lean_ctor_set(v___x_758_, 2, v___f_754_);
lean_ctor_set(v___x_758_, 3, v___f_756_);
lean_ctor_set(v___x_758_, 4, v___f_755_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t v_sz_759_, size_t v_i_760_, lean_object* v_bs_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_759_, v_i_760_, v_bs_761_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object* v_sz_771_, lean_object* v_i_772_, lean_object* v_bs_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
size_t v_sz_boxed_782_; size_t v_i_boxed_783_; lean_object* v_res_784_; 
v_sz_boxed_782_ = lean_unbox_usize(v_sz_771_);
lean_dec(v_sz_771_);
v_i_boxed_783_ = lean_unbox_usize(v_i_772_);
lean_dec(v_i_772_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_782_, v_i_boxed_783_, v_bs_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object* v_baseMonadInfo_788_, lean_object* v_00_u03b1_789_){
_start:
{
lean_object* v_u_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_u_790_ = lean_ctor_get(v_baseMonadInfo_788_, 1);
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_792_ = lean_box(0);
lean_inc(v_u_790_);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v_u_790_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_mkConst(v___x_791_, v___x_793_);
v___x_795_ = l_Lean_Expr_app___override(v___x_794_, v_00_u03b1_789_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object* v_baseMonadInfo_796_, lean_object* v_00_u03b1_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_796_, v_00_u03b1_797_);
lean_dec_ref(v_baseMonadInfo_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object* v_runInBase_804_, lean_object* v_e_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_814_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2));
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_mk_empty_array_with_capacity(v___x_815_);
v___x_817_ = lean_array_push(v___x_816_, v_e_805_);
v___x_818_ = l_Lean_Meta_mkAppM(v___x_814_, v___x_817_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc_ref(v___y_806_);
v___x_820_ = lean_apply_9(v_runInBase_804_, v_a_819_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
return v___x_820_;
}
else
{
lean_dec_ref(v_runInBase_804_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object* v_runInBase_821_, lean_object* v_e_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_821_, v_e_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object* v_description_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_837_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1, &l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1);
v___x_838_ = lean_box(0);
v___x_839_ = lean_apply_1(v_description_835_, v___x_838_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_837_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object* v_k_841_, lean_object* v_r_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; 
lean_inc(v___y_849_);
lean_inc_ref(v___y_848_);
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc_ref(v___y_843_);
v___x_851_ = lean_apply_8(v_k_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, lean_box(0));
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_mk_empty_array_with_capacity(v___x_853_);
v___x_855_ = lean_array_push(v___x_854_, v_r_842_);
v___x_856_ = 0;
v___x_857_ = 1;
v___x_858_ = 1;
v___x_859_ = l_Lean_Meta_mkLambdaFVars(v___x_855_, v_a_852_, v___x_856_, v___x_857_, v___x_856_, v___x_857_, v___x_858_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec_ref(v___x_855_);
return v___x_859_;
}
else
{
lean_dec_ref(v_r_842_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object* v_k_860_, lean_object* v_r_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_k_860_, v_r_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object* v_a_871_, lean_object* v_r_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
lean_inc_ref(v___y_873_);
v___x_881_ = lean_apply_8(v_a_871_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, lean_box(0));
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; uint8_t v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_mk_empty_array_with_capacity(v___x_883_);
v___x_885_ = lean_array_push(v___x_884_, v_r_872_);
v___x_886_ = 0;
v___x_887_ = 1;
v___x_888_ = 1;
v___x_889_ = l_Lean_Meta_mkLambdaFVars(v___x_885_, v_a_882_, v___x_886_, v___x_887_, v___x_886_, v___x_887_, v___x_888_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec_ref(v___x_885_);
return v___x_889_;
}
else
{
lean_dec_ref(v_r_872_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object* v_a_890_, lean_object* v_r_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_890_, v_r_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object* v_k_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc_ref(v___y_902_);
v___x_911_ = lean_apply_9(v_k_901_, v_b_905_, v___y_902_, v___y_903_, v___y_904_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, lean_box(0));
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_912_, v___y_913_, v___y_914_, v___y_915_, v_b_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object* v_name_923_, uint8_t v_bi_924_, lean_object* v_type_925_, lean_object* v_k_926_, uint8_t v_kind_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___f_936_; lean_object* v___x_937_; 
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc_ref(v___y_928_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_936_, 0, v_k_926_);
lean_closure_set(v___f_936_, 1, v___y_928_);
lean_closure_set(v___f_936_, 2, v___y_929_);
lean_closure_set(v___f_936_, 3, v___y_930_);
v___x_937_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_923_, v_bi_924_, v_type_925_, v___f_936_, v_kind_927_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_937_) == 0)
{
return v___x_937_;
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object* v_name_946_, lean_object* v_bi_947_, lean_object* v_type_948_, lean_object* v_k_949_, lean_object* v_kind_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v_bi_boxed_959_; uint8_t v_kind_boxed_960_; lean_object* v_res_961_; 
v_bi_boxed_959_ = lean_unbox(v_bi_947_);
v_kind_boxed_960_ = lean_unbox(v_kind_950_);
v_res_961_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_946_, v_bi_boxed_959_, v_type_948_, v_k_949_, v_kind_boxed_960_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object* v_name_962_, lean_object* v_type_963_, lean_object* v_k_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = 0;
v___x_974_ = 0;
v___x_975_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_962_, v___x_973_, v_type_963_, v_k_964_, v___x_974_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object* v_name_976_, lean_object* v_type_977_, lean_object* v_k_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_976_, v_type_977_, v_k_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3));
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object* v_a_997_, lean_object* v_getCont_998_, lean_object* v_resultName_999_, lean_object* v_resultType_1000_, lean_object* v___f_1001_, lean_object* v_baseMonadInfo_1002_, lean_object* v_casesOnWrapper_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_getFVarFromUserName(v_a_997_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___x_1014_ = lean_apply_8(v_getCont_998_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, lean_box(0));
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1017_ = l_Lean_Core_mkFreshUserName(v___x_1016_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1019_, 0, v_a_1015_);
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4, &l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4);
v___x_1022_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1018_, v___x_1021_, v___f_1019_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
lean_inc_ref(v_resultType_1000_);
v___x_1024_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_999_, v_resultType_1000_, v___f_1001_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_doBlockResultType_1026_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v_doBlockResultType_1026_ = lean_ctor_get(v___y_1004_, 3);
lean_inc_ref(v_doBlockResultType_1026_);
v___x_1027_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1026_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1041_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1041_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_u_1032_; lean_object* v_v_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v_u_1032_ = lean_ctor_get(v_baseMonadInfo_1002_, 1);
v_v_1033_ = lean_ctor_get(v_baseMonadInfo_1002_, 2);
lean_inc(v_v_1033_);
v___x_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_v_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1020_);
lean_inc(v_u_1032_);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_u_1032_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_mkConst(v_casesOnWrapper_1003_, v___x_1035_);
v___x_1037_ = l_Lean_mkApp5(v___x_1036_, v_resultType_1000_, v_a_1028_, v_a_1013_, v_a_1023_, v_a_1025_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1037_);
v___x_1039_ = v___x_1030_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_dec(v_a_1025_);
lean_dec(v_a_1023_);
lean_dec(v_a_1013_);
lean_dec(v_casesOnWrapper_1003_);
lean_dec_ref(v_resultType_1000_);
return v___x_1027_;
}
}
else
{
lean_dec(v_a_1023_);
lean_dec(v_a_1013_);
lean_dec(v_casesOnWrapper_1003_);
lean_dec_ref(v_resultType_1000_);
return v___x_1024_;
}
}
else
{
lean_dec(v_a_1013_);
lean_dec(v_casesOnWrapper_1003_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v_resultType_1000_);
lean_dec(v_resultName_999_);
return v___x_1022_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_1015_);
lean_dec(v_a_1013_);
lean_dec(v_casesOnWrapper_1003_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v_resultType_1000_);
lean_dec(v_resultName_999_);
v_a_1042_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1017_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1017_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1013_);
lean_dec(v_casesOnWrapper_1003_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v_resultType_1000_);
lean_dec(v_resultName_999_);
v_a_1050_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1014_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1014_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_dec(v_casesOnWrapper_1003_);
lean_dec_ref(v___f_1001_);
lean_dec_ref(v_resultType_1000_);
lean_dec(v_resultName_999_);
lean_dec_ref(v_getCont_998_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object* v_a_1058_, lean_object* v_getCont_1059_, lean_object* v_resultName_1060_, lean_object* v_resultType_1061_, lean_object* v___f_1062_, lean_object* v_baseMonadInfo_1063_, lean_object* v_casesOnWrapper_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1058_, v_getCont_1059_, v_resultName_1060_, v_resultType_1061_, v___f_1062_, v_baseMonadInfo_1063_, v_casesOnWrapper_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_baseMonadInfo_1063_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object* v_getCont_1077_, lean_object* v_baseMonadInfo_1078_, lean_object* v_casesOnWrapper_1079_, lean_object* v_restoreCont_1080_, lean_object* v_dec_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1091_ = l_Lean_Core_mkFreshUserName(v___x_1090_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_resultName_1093_; lean_object* v_resultType_1094_; lean_object* v_k_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1107_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v_resultName_1093_ = lean_ctor_get(v_dec_1081_, 0);
v_resultType_1094_ = lean_ctor_get(v_dec_1081_, 1);
v_k_1095_ = lean_ctor_get(v_dec_1081_, 2);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_dec_1081_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1097_ = v_dec_1081_;
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_k_1095_);
lean_inc(v_resultType_1094_);
lean_inc(v_resultName_1093_);
lean_dec(v_dec_1081_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1104_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1099_, 0, v_k_1095_);
lean_inc_ref(v_baseMonadInfo_1078_);
lean_inc_ref(v_resultType_1094_);
lean_inc(v_a_1092_);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed), 15, 7);
lean_closure_set(v___f_1100_, 0, v_a_1092_);
lean_closure_set(v___f_1100_, 1, v_getCont_1077_);
lean_closure_set(v___f_1100_, 2, v_resultName_1093_);
lean_closure_set(v___f_1100_, 3, v_resultType_1094_);
lean_closure_set(v___f_1100_, 4, v___f_1099_);
lean_closure_set(v___f_1100_, 5, v_baseMonadInfo_1078_);
lean_closure_set(v___f_1100_, 6, v_casesOnWrapper_1079_);
v___x_1101_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1078_, v_resultType_1094_);
lean_dec_ref(v_baseMonadInfo_1078_);
v___x_1102_ = 0;
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 2, v___f_1100_);
lean_ctor_set(v___x_1097_, 1, v___x_1101_);
lean_ctor_set(v___x_1097_, 0, v_a_1092_);
v___x_1104_ = v___x_1097_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1092_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v___f_1100_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*3, v___x_1102_);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1105_ = lean_apply_9(v_restoreCont_1080_, v___x_1104_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, lean_box(0));
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_dec_1081_);
lean_dec_ref(v_restoreCont_1080_);
lean_dec(v_casesOnWrapper_1079_);
lean_dec_ref(v_baseMonadInfo_1078_);
lean_dec_ref(v_getCont_1077_);
v_a_1108_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1091_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1091_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object* v_getCont_1116_, lean_object* v_baseMonadInfo_1117_, lean_object* v_casesOnWrapper_1118_, lean_object* v_restoreCont_1119_, lean_object* v_dec_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1116_, v_baseMonadInfo_1117_, v_casesOnWrapper_1118_, v_restoreCont_1119_, v_dec_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object* v_baseMonadInfo_1130_, lean_object* v_stM_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1130_, v___y_1132_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc_ref(v___y_1133_);
v___x_1142_ = lean_apply_9(v_stM_1131_, v___x_1141_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object* v_baseMonadInfo_1143_, lean_object* v_stM_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1143_, v_stM_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_baseMonadInfo_1143_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object* v_m_1155_, lean_object* v_baseMonadInfo_1156_, lean_object* v_optionTWrapper_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
lean_inc(v___y_1162_);
lean_inc_ref(v___y_1161_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc_ref(v___y_1158_);
v___x_1166_ = lean_apply_8(v_m_1155_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, lean_box(0));
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1181_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1181_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1181_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_u_1171_; lean_object* v_v_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v_u_1171_ = lean_ctor_get(v_baseMonadInfo_1156_, 1);
v_v_1172_ = lean_ctor_get(v_baseMonadInfo_1156_, 2);
v___x_1173_ = lean_box(0);
lean_inc(v_v_1172_);
v___x_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_v_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
lean_inc(v_u_1171_);
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_u_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_mkConst(v_optionTWrapper_1157_, v___x_1175_);
v___x_1177_ = l_Lean_Expr_app___override(v___x_1176_, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1177_);
v___x_1179_ = v___x_1169_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_dec(v_optionTWrapper_1157_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object* v_m_1182_, lean_object* v_baseMonadInfo_1183_, lean_object* v_optionTWrapper_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1182_, v_baseMonadInfo_1183_, v_optionTWrapper_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v_baseMonadInfo_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object* v_baseMonadInfo_1194_, lean_object* v_optionTWrapper_1195_, lean_object* v_casesOnWrapper_1196_, lean_object* v_getCont_1197_, lean_object* v_base_1198_){
_start:
{
lean_object* v_description_1199_; lean_object* v_m_1200_; lean_object* v_stM_1201_; lean_object* v_runInBase_1202_; lean_object* v_restoreCont_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1215_; 
v_description_1199_ = lean_ctor_get(v_base_1198_, 0);
v_m_1200_ = lean_ctor_get(v_base_1198_, 1);
v_stM_1201_ = lean_ctor_get(v_base_1198_, 2);
v_runInBase_1202_ = lean_ctor_get(v_base_1198_, 3);
v_restoreCont_1203_ = lean_ctor_get(v_base_1198_, 4);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_base_1198_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1205_ = v_base_1198_;
v_isShared_1206_ = v_isSharedCheck_1215_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_restoreCont_1203_);
lean_inc(v_runInBase_1202_);
lean_inc(v_stM_1201_);
lean_inc(v_m_1200_);
lean_inc(v_description_1199_);
lean_dec(v_base_1198_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1215_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1213_; 
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1207_, 0, v_runInBase_1202_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1), 2, 1);
lean_closure_set(v___f_1208_, 0, v_description_1199_);
lean_inc_ref_n(v_baseMonadInfo_1194_, 2);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed), 13, 4);
lean_closure_set(v___f_1209_, 0, v_getCont_1197_);
lean_closure_set(v___f_1209_, 1, v_baseMonadInfo_1194_);
lean_closure_set(v___f_1209_, 2, v_casesOnWrapper_1196_);
lean_closure_set(v___f_1209_, 3, v_restoreCont_1203_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed), 11, 2);
lean_closure_set(v___f_1210_, 0, v_baseMonadInfo_1194_);
lean_closure_set(v___f_1210_, 1, v_stM_1201_);
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed), 11, 3);
lean_closure_set(v___f_1211_, 0, v_m_1200_);
lean_closure_set(v___f_1211_, 1, v_baseMonadInfo_1194_);
lean_closure_set(v___f_1211_, 2, v_optionTWrapper_1195_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 4, v___f_1209_);
lean_ctor_set(v___x_1205_, 3, v___f_1207_);
lean_ctor_set(v___x_1205_, 2, v___f_1210_);
lean_ctor_set(v___x_1205_, 1, v___f_1211_);
lean_ctor_set(v___x_1205_, 0, v___f_1208_);
v___x_1213_ = v___x_1205_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___f_1208_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___f_1211_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v___f_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v___f_1209_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object* v_00_u03b1_1216_, lean_object* v_name_1217_, uint8_t v_bi_1218_, lean_object* v_type_1219_, lean_object* v_k_1220_, uint8_t v_kind_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_1217_, v_bi_1218_, v_type_1219_, v_k_1220_, v_kind_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_name_1232_, lean_object* v_bi_1233_, lean_object* v_type_1234_, lean_object* v_k_1235_, lean_object* v_kind_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v_bi_boxed_1245_; uint8_t v_kind_boxed_1246_; lean_object* v_res_1247_; 
v_bi_boxed_1245_ = lean_unbox(v_bi_1233_);
v_kind_boxed_1246_ = lean_unbox(v_kind_1236_);
v_res_1247_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_1231_, v_name_1232_, v_bi_boxed_1245_, v_type_1234_, v_k_1235_, v_kind_boxed_1246_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object* v_00_u03b1_1248_, lean_object* v_name_1249_, lean_object* v_type_1250_, lean_object* v_k_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1249_, v_type_1250_, v_k_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_name_1262_, lean_object* v_type_1263_, lean_object* v_k_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(v_00_u03b1_1261_, v_name_1262_, v_type_1263_, v_k_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object* v_baseMonadInfo_1277_, lean_object* v_getCont_1278_, lean_object* v_00_u03b1_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1288_; 
lean_inc(v_a_1286_);
lean_inc_ref(v_a_1285_);
lean_inc(v_a_1284_);
lean_inc_ref(v_a_1283_);
lean_inc(v_a_1282_);
lean_inc_ref(v_a_1281_);
lean_inc_ref(v_a_1280_);
v___x_1288_ = lean_apply_8(v_getCont_1278_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, lean_box(0));
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1311_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1311_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1311_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_u_1293_; lean_object* v_resultType_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1309_; 
v_u_1293_ = lean_ctor_get(v_baseMonadInfo_1277_, 1);
v_resultType_1294_ = lean_ctor_get(v_a_1289_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_a_1289_, 1);
lean_dec(v_unused_1310_);
v___x_1296_ = v_a_1289_;
v_isShared_1297_ = v_isSharedCheck_1309_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_resultType_1294_);
lean_dec(v_a_1289_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1309_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_box(0);
lean_inc(v_u_1293_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 1);
lean_ctor_set(v___x_1296_, 1, v___x_1298_);
lean_ctor_set(v___x_1296_, 0, v_u_1293_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_u_1293_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
lean_inc(v_u_1293_);
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_u_1293_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
v___x_1303_ = l_Lean_mkConst(v___x_1301_, v___x_1302_);
v___x_1304_ = l_Lean_mkAppB(v___x_1303_, v_resultType_1294_, v_00_u03b1_1279_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1304_);
v___x_1306_ = v___x_1291_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_00_u03b1_1279_);
v_a_1312_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1288_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1288_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object* v_baseMonadInfo_1320_, lean_object* v_getCont_1321_, lean_object* v_00_u03b1_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1320_, v_getCont_1321_, v_00_u03b1_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec_ref(v_baseMonadInfo_1320_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object* v_k_1332_, lean_object* v_r_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1342_ = lean_apply_8(v_k_1332_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, lean_box(0));
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; uint8_t v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_n(v_a_1343_, 2);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_mk_empty_array_with_capacity(v___x_1344_);
v___x_1346_ = lean_array_push(v___x_1345_, v_r_1333_);
v___x_1347_ = 0;
v___x_1348_ = 1;
v___x_1349_ = 1;
v___x_1350_ = l_Lean_Meta_mkLambdaFVars(v___x_1346_, v_a_1343_, v___x_1347_, v___x_1348_, v___x_1347_, v___x_1348_, v___x_1349_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec_ref(v___x_1346_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1352_ = lean_infer_type(v_a_1343_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1351_);
lean_ctor_set(v___x_1357_, 1, v_a_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1351_);
v_a_1362_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1352_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1352_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1343_);
v_a_1370_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1350_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1350_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v_r_1333_);
v_a_1378_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1342_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1342_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object* v_k_1386_, lean_object* v_r_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_k_1386_, v_r_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object* v_k_1397_, lean_object* v_r_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc_ref(v_r_1398_);
v___x_1407_ = lean_apply_9(v_k_1397_, v_r_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, lean_box(0));
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; uint8_t v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_mk_empty_array_with_capacity(v___x_1409_);
v___x_1411_ = lean_array_push(v___x_1410_, v_r_1398_);
v___x_1412_ = 0;
v___x_1413_ = 1;
v___x_1414_ = 1;
v___x_1415_ = l_Lean_Meta_mkLambdaFVars(v___x_1411_, v_a_1408_, v___x_1412_, v___x_1413_, v___x_1412_, v___x_1413_, v___x_1414_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref(v___x_1411_);
return v___x_1415_;
}
else
{
lean_dec_ref(v_r_1398_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object* v_k_1416_, lean_object* v_r_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_k_1416_, v_r_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object* v_a_1427_, lean_object* v_getCont_1428_, lean_object* v_resultName_1429_, lean_object* v_resultType_1430_, lean_object* v___f_1431_, lean_object* v_baseMonadInfo_1432_, lean_object* v_casesOnWrapper_1433_, lean_object* v_00_u03b5_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Meta_getFVarFromUserName(v_a_1427_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1445_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc_ref(v___y_1435_);
v___x_1445_ = lean_apply_8(v_getCont_1428_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, lean_box(0));
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1448_ = l_Lean_Core_mkFreshUserName(v___x_1447_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v_resultType_1450_; lean_object* v_k_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1492_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v_resultType_1450_ = lean_ctor_get(v_a_1446_, 0);
v_k_1451_ = lean_ctor_get(v_a_1446_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_a_1446_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1453_ = v_a_1446_;
v_isShared_1454_ = v_isSharedCheck_1492_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_k_1451_);
lean_inc(v_resultType_1450_);
lean_dec(v_a_1446_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1492_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___f_1455_; lean_object* v___x_1456_; 
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1455_, 0, v_k_1451_);
v___x_1456_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1449_, v_resultType_1450_, v___f_1455_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
lean_inc_ref(v_resultType_1430_);
v___x_1458_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1429_, v_resultType_1430_, v___f_1431_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1483_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1483_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1483_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_fst_1463_; lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1482_; 
v_fst_1463_ = lean_ctor_get(v_a_1459_, 0);
v_snd_1464_ = lean_ctor_get(v_a_1459_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1459_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1466_ = v_a_1459_;
v_isShared_1467_ = v_isSharedCheck_1482_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_inc(v_fst_1463_);
lean_dec(v_a_1459_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1482_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_u_1468_; lean_object* v_v_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v_u_1468_ = lean_ctor_get(v_baseMonadInfo_1432_, 1);
v_v_1469_ = lean_ctor_get(v_baseMonadInfo_1432_, 2);
v___x_1470_ = lean_box(0);
lean_inc(v_v_1469_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 1);
lean_ctor_set(v___x_1466_, 1, v___x_1470_);
lean_ctor_set(v___x_1466_, 0, v_v_1469_);
v___x_1472_ = v___x_1466_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
lean_inc(v_u_1468_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 1);
lean_ctor_set(v___x_1453_, 1, v___x_1472_);
lean_ctor_set(v___x_1453_, 0, v_u_1468_);
v___x_1474_ = v___x_1453_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_u_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1475_ = l_Lean_mkConst(v_casesOnWrapper_1433_, v___x_1474_);
v___x_1476_ = l_Lean_mkApp6(v___x_1475_, v_00_u03b5_1434_, v_resultType_1430_, v_snd_1464_, v_a_1444_, v_a_1457_, v_fst_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1476_);
v___x_1478_ = v___x_1461_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_a_1457_);
lean_del_object(v___x_1453_);
lean_dec(v_a_1444_);
lean_dec_ref(v_00_u03b5_1434_);
lean_dec(v_casesOnWrapper_1433_);
lean_dec_ref(v_resultType_1430_);
v_a_1484_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1458_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1458_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_del_object(v___x_1453_);
lean_dec(v_a_1444_);
lean_dec_ref(v_00_u03b5_1434_);
lean_dec(v_casesOnWrapper_1433_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v_resultType_1430_);
lean_dec(v_resultName_1429_);
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_a_1446_);
lean_dec(v_a_1444_);
lean_dec_ref(v_00_u03b5_1434_);
lean_dec(v_casesOnWrapper_1433_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v_resultType_1430_);
lean_dec(v_resultName_1429_);
v_a_1493_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1448_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1448_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1444_);
lean_dec_ref(v_00_u03b5_1434_);
lean_dec(v_casesOnWrapper_1433_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v_resultType_1430_);
lean_dec(v_resultName_1429_);
v_a_1501_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1445_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1445_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1434_);
lean_dec(v_casesOnWrapper_1433_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v_resultType_1430_);
lean_dec(v_resultName_1429_);
lean_dec_ref(v_getCont_1428_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object* v_a_1509_, lean_object* v_getCont_1510_, lean_object* v_resultName_1511_, lean_object* v_resultType_1512_, lean_object* v___f_1513_, lean_object* v_baseMonadInfo_1514_, lean_object* v_casesOnWrapper_1515_, lean_object* v_00_u03b5_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1509_, v_getCont_1510_, v_resultName_1511_, v_resultType_1512_, v___f_1513_, v_baseMonadInfo_1514_, v_casesOnWrapper_1515_, v_00_u03b5_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_baseMonadInfo_1514_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object* v_baseMonadInfo_1526_, lean_object* v_getCont_1527_, lean_object* v_casesOnWrapper_1528_, lean_object* v_00_u03b5_1529_, lean_object* v_restoreCont_1530_, lean_object* v_dec_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1541_ = l_Lean_Core_mkFreshUserName(v___x_1540_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_resultName_1543_; lean_object* v_resultType_1544_; lean_object* v_k_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1566_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v_resultName_1543_ = lean_ctor_get(v_dec_1531_, 0);
v_resultType_1544_ = lean_ctor_get(v_dec_1531_, 1);
v_k_1545_ = lean_ctor_get(v_dec_1531_, 2);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_dec_1531_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1547_ = v_dec_1531_;
v_isShared_1548_ = v_isSharedCheck_1566_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_k_1545_);
lean_inc(v_resultType_1544_);
lean_inc(v_resultName_1543_);
lean_dec(v_dec_1531_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1566_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; 
lean_inc_ref(v_resultType_1544_);
lean_inc_ref(v_getCont_1527_);
v___x_1549_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1526_, v_getCont_1527_, v_resultType_1544_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; uint8_t v___x_1553_; lean_object* v___x_1555_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1551_, 0, v_k_1545_);
lean_inc(v_a_1542_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed), 16, 8);
lean_closure_set(v___f_1552_, 0, v_a_1542_);
lean_closure_set(v___f_1552_, 1, v_getCont_1527_);
lean_closure_set(v___f_1552_, 2, v_resultName_1543_);
lean_closure_set(v___f_1552_, 3, v_resultType_1544_);
lean_closure_set(v___f_1552_, 4, v___f_1551_);
lean_closure_set(v___f_1552_, 5, v_baseMonadInfo_1526_);
lean_closure_set(v___f_1552_, 6, v_casesOnWrapper_1528_);
lean_closure_set(v___f_1552_, 7, v_00_u03b5_1529_);
v___x_1553_ = 0;
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 2, v___f_1552_);
lean_ctor_set(v___x_1547_, 1, v_a_1550_);
lean_ctor_set(v___x_1547_, 0, v_a_1542_);
v___x_1555_ = v___x_1547_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1542_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_a_1550_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v___f_1552_);
v___x_1555_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; 
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*3, v___x_1553_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
lean_inc(v___y_1534_);
lean_inc_ref(v___y_1533_);
lean_inc_ref(v___y_1532_);
v___x_1556_ = lean_apply_9(v_restoreCont_1530_, v___x_1555_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, lean_box(0));
return v___x_1556_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1547_);
lean_dec_ref(v_k_1545_);
lean_dec_ref(v_resultType_1544_);
lean_dec(v_resultName_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_restoreCont_1530_);
lean_dec_ref(v_00_u03b5_1529_);
lean_dec(v_casesOnWrapper_1528_);
lean_dec_ref(v_getCont_1527_);
lean_dec_ref(v_baseMonadInfo_1526_);
v_a_1558_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1549_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1549_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v_dec_1531_);
lean_dec_ref(v_restoreCont_1530_);
lean_dec_ref(v_00_u03b5_1529_);
lean_dec(v_casesOnWrapper_1528_);
lean_dec_ref(v_getCont_1527_);
lean_dec_ref(v_baseMonadInfo_1526_);
v_a_1567_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1541_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1541_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object* v_baseMonadInfo_1575_, lean_object* v_getCont_1576_, lean_object* v_casesOnWrapper_1577_, lean_object* v_00_u03b5_1578_, lean_object* v_restoreCont_1579_, lean_object* v_dec_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_baseMonadInfo_1575_, v_getCont_1576_, v_casesOnWrapper_1577_, v_00_u03b5_1578_, v_restoreCont_1579_, v_dec_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1589_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object* v_00_u03b5_1596_, lean_object* v_description_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1599_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1);
v___x_1600_ = l_Lean_MessageData_ofExpr(v_00_u03b5_1596_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_apply_1(v_description_1597_, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1603_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object* v_baseMonadInfo_1607_, lean_object* v_getCont_1608_, lean_object* v_stM_1609_, lean_object* v_00_u03b1_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1607_, v_getCont_1608_, v_00_u03b1_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
lean_inc_ref(v___y_1611_);
v___x_1621_ = lean_apply_9(v_stM_1609_, v_a_1620_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, lean_box(0));
return v___x_1621_;
}
else
{
lean_dec_ref(v_stM_1609_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object* v_baseMonadInfo_1622_, lean_object* v_getCont_1623_, lean_object* v_stM_1624_, lean_object* v_00_u03b1_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1622_, v_getCont_1623_, v_stM_1624_, v_00_u03b1_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v_baseMonadInfo_1622_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object* v_runInBase_1639_, lean_object* v_e_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1649_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1));
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_array_push(v___x_1651_, v_e_1640_);
v___x_1653_ = l_Lean_Meta_mkAppM(v___x_1649_, v___x_1652_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc_ref(v___y_1641_);
v___x_1655_ = lean_apply_9(v_runInBase_1639_, v_a_1654_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, lean_box(0));
return v___x_1655_;
}
else
{
lean_dec_ref(v_runInBase_1639_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object* v_runInBase_1656_, lean_object* v_e_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1656_, v_e_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object* v_m_1667_, lean_object* v_baseMonadInfo_1668_, lean_object* v_exceptTWrapper_1669_, lean_object* v_00_u03b5_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc_ref(v___y_1671_);
v___x_1679_ = lean_apply_8(v_m_1667_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1694_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1694_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1694_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_u_1684_; lean_object* v_v_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v_u_1684_ = lean_ctor_get(v_baseMonadInfo_1668_, 1);
v_v_1685_ = lean_ctor_get(v_baseMonadInfo_1668_, 2);
v___x_1686_ = lean_box(0);
lean_inc(v_v_1685_);
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_v_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
lean_inc(v_u_1684_);
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_u_1684_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_mkConst(v_exceptTWrapper_1669_, v___x_1688_);
v___x_1690_ = l_Lean_mkAppB(v___x_1689_, v_00_u03b5_1670_, v_a_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1690_);
v___x_1692_ = v___x_1682_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1670_);
lean_dec(v_exceptTWrapper_1669_);
return v___x_1679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object* v_m_1695_, lean_object* v_baseMonadInfo_1696_, lean_object* v_exceptTWrapper_1697_, lean_object* v_00_u03b5_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1695_, v_baseMonadInfo_1696_, v_exceptTWrapper_1697_, v_00_u03b5_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v_baseMonadInfo_1696_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object* v_baseMonadInfo_1708_, lean_object* v_exceptTWrapper_1709_, lean_object* v_casesOnWrapper_1710_, lean_object* v_getCont_1711_, lean_object* v_00_u03b5_1712_, lean_object* v_base_1713_){
_start:
{
lean_object* v_description_1714_; lean_object* v_m_1715_; lean_object* v_stM_1716_; lean_object* v_runInBase_1717_; lean_object* v_restoreCont_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1730_; 
v_description_1714_ = lean_ctor_get(v_base_1713_, 0);
v_m_1715_ = lean_ctor_get(v_base_1713_, 1);
v_stM_1716_ = lean_ctor_get(v_base_1713_, 2);
v_runInBase_1717_ = lean_ctor_get(v_base_1713_, 3);
v_restoreCont_1718_ = lean_ctor_get(v_base_1713_, 4);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_base_1713_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1720_ = v_base_1713_;
v_isShared_1721_ = v_isSharedCheck_1730_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_restoreCont_1718_);
lean_inc(v_runInBase_1717_);
lean_inc(v_stM_1716_);
lean_inc(v_m_1715_);
lean_inc(v_description_1714_);
lean_dec(v_base_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1730_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___x_1728_; 
lean_inc_ref_n(v_00_u03b5_1712_, 2);
lean_inc_ref(v_getCont_1711_);
lean_inc_ref_n(v_baseMonadInfo_1708_, 2);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed), 14, 5);
lean_closure_set(v___f_1722_, 0, v_baseMonadInfo_1708_);
lean_closure_set(v___f_1722_, 1, v_getCont_1711_);
lean_closure_set(v___f_1722_, 2, v_casesOnWrapper_1710_);
lean_closure_set(v___f_1722_, 3, v_00_u03b5_1712_);
lean_closure_set(v___f_1722_, 4, v_restoreCont_1718_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4), 3, 2);
lean_closure_set(v___f_1723_, 0, v_00_u03b5_1712_);
lean_closure_set(v___f_1723_, 1, v_description_1714_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed), 12, 3);
lean_closure_set(v___f_1724_, 0, v_baseMonadInfo_1708_);
lean_closure_set(v___f_1724_, 1, v_getCont_1711_);
lean_closure_set(v___f_1724_, 2, v_stM_1716_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed), 10, 1);
lean_closure_set(v___f_1725_, 0, v_runInBase_1717_);
v___f_1726_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed), 12, 4);
lean_closure_set(v___f_1726_, 0, v_m_1715_);
lean_closure_set(v___f_1726_, 1, v_baseMonadInfo_1708_);
lean_closure_set(v___f_1726_, 2, v_exceptTWrapper_1709_);
lean_closure_set(v___f_1726_, 3, v_00_u03b5_1712_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v___f_1722_);
lean_ctor_set(v___x_1720_, 3, v___f_1725_);
lean_ctor_set(v___x_1720_, 2, v___f_1724_);
lean_ctor_set(v___x_1720_, 1, v___f_1726_);
lean_ctor_set(v___x_1720_, 0, v___f_1723_);
v___x_1728_ = v___x_1720_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___f_1723_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___f_1726_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v___f_1724_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v___f_1725_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v___f_1722_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object* v_baseMonadInfo_1740_, lean_object* v_00_u03c1_1741_, lean_object* v_m_1742_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1));
v___x_1744_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4));
v___x_1745_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5));
v___x_1746_ = l_Lean_Elab_Do_ControlStack_exceptT(v_baseMonadInfo_1740_, v___x_1743_, v___x_1744_, v___x_1745_, v_00_u03c1_1741_, v_m_1742_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_1750_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
if (lean_obj_tag(v_a_1759_) == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_del_object(v___x_1761_);
v___x_1763_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1);
v___x_1764_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1763_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1767_; 
v_val_1765_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v_a_1759_, 1);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v_val_1765_);
v___x_1767_ = v___x_1761_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_val_1765_);
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
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1758_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1758_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object* v_baseMonadInfo_1795_, lean_object* v_m_1796_){
_start:
{
lean_object* v_getCont_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_getCont_1797_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__0));
v___x_1798_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__2));
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__4));
v___x_1800_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1795_, v___x_1798_, v___x_1799_, v_getCont_1797_, v_m_1796_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_1804_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
if (lean_obj_tag(v_a_1813_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_del_object(v___x_1815_);
v___x_1817_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1);
v___x_1818_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1817_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1818_;
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1821_; 
v_val_1819_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_val_1819_);
lean_dec_ref_known(v_a_1813_, 1);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_val_1819_);
v___x_1821_ = v___x_1815_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_val_1819_);
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
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1812_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1812_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v___y_1832_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object* v_baseMonadInfo_1849_, lean_object* v_m_1850_){
_start:
{
lean_object* v_getCont_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_getCont_1851_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__0));
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__2));
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__4));
v___x_1854_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1849_, v___x_1852_, v___x_1853_, v_getCont_1851_, v_m_1850_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object* v_mi_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_m_1866_; lean_object* v_u_1867_; lean_object* v_v_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_m_1866_ = lean_ctor_get(v_mi_1858_, 0);
lean_inc_ref(v_m_1866_);
v_u_1867_ = lean_ctor_get(v_mi_1858_, 1);
lean_inc(v_u_1867_);
v_v_1868_ = lean_ctor_get(v_mi_1858_, 2);
lean_inc(v_v_1868_);
lean_dec_ref(v_mi_1858_);
v___x_1869_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1));
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_v_1868_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_u_1867_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_mkConst(v___x_1869_, v___x_1872_);
v___x_1874_ = l_Lean_Expr_app___override(v___x_1873_, v_m_1866_);
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Lean_Elab_Term_mkInstMVar(v___x_1874_, v___x_1875_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object* v_mi_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
return v_res_1885_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0));
v___x_1888_ = l_Lean_stringToMessageData(v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2));
v___x_1891_ = l_Lean_stringToMessageData(v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4));
v___x_1894_ = l_Lean_stringToMessageData(v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6));
v___x_1897_ = l_Lean_stringToMessageData(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object* v_msg_1898_, lean_object* v_expected_1899_, lean_object* v_actual_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v___x_1906_; 
lean_inc_ref(v_actual_1900_);
lean_inc_ref(v_expected_1899_);
v___x_1906_ = l_Lean_Meta_isExprDefEq(v_expected_1899_, v_actual_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1930_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1930_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1930_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
uint8_t v___x_1911_; 
v___x_1911_ = lean_unbox(v_a_1907_);
lean_dec(v_a_1907_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_del_object(v___x_1909_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
v___x_1913_ = l_Lean_stringToMessageData(v_msg_1898_);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_MessageData_ofExpr(v_expected_1899_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_MessageData_ofExpr(v_actual_1900_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1924_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_dec_ref(v_actual_1900_);
lean_dec_ref(v_expected_1899_);
lean_dec_ref(v_msg_1898_);
v___x_1926_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1926_);
v___x_1928_ = v___x_1909_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_actual_1900_);
lean_dec_ref(v_expected_1899_);
lean_dec_ref(v_msg_1898_);
v_a_1931_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1906_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1906_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object* v_msg_1939_, lean_object* v_expected_1940_, lean_object* v_actual_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1939_, v_expected_1940_, v_actual_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object* v_msg_1948_, lean_object* v_expected_1949_, lean_object* v_actual_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1948_, v_expected_1949_, v_actual_1950_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object* v_msg_1960_, lean_object* v_expected_1961_, lean_object* v_actual_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_1960_, v_expected_1961_, v_actual_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_a_1963_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object* v_base_1977_, uint8_t v_hasContinue_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_m_1987_; lean_object* v_runInBase_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2046_; 
v_m_1987_ = lean_ctor_get(v_base_1977_, 1);
v_runInBase_1988_ = lean_ctor_get(v_base_1977_, 3);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_base_1977_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; 
v_unused_2047_ = lean_ctor_get(v_base_1977_, 4);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_base_1977_, 2);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_base_1977_, 0);
lean_dec(v_unused_2049_);
v___x_1990_ = v_base_1977_;
v_isShared_1991_ = v_isSharedCheck_2046_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_runInBase_1988_);
lean_inc(v_m_1987_);
lean_dec(v_base_1977_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2046_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; 
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1984_);
lean_inc(v_a_1983_);
lean_inc_ref(v_a_1982_);
lean_inc(v_a_1981_);
lean_inc_ref(v_a_1980_);
lean_inc_ref(v_a_1979_);
v___x_1992_ = lean_apply_8(v_m_1987_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, lean_box(0));
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_monadInfo_1993_; lean_object* v_a_1994_; lean_object* v_doBlockResultType_1995_; lean_object* v_u_1996_; lean_object* v_v_1997_; lean_object* v_cachedPUnit_1998_; lean_object* v_cachedPUnitUnit_1999_; lean_object* v___x_2001_; 
v_monadInfo_1993_ = lean_ctor_get(v_a_1979_, 0);
v_a_1994_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_n(v_a_1994_, 2);
lean_dec_ref_known(v___x_1992_, 1);
v_doBlockResultType_1995_ = lean_ctor_get(v_a_1979_, 3);
v_u_1996_ = lean_ctor_get(v_monadInfo_1993_, 1);
v_v_1997_ = lean_ctor_get(v_monadInfo_1993_, 2);
v_cachedPUnit_1998_ = lean_ctor_get(v_monadInfo_1993_, 3);
v_cachedPUnitUnit_1999_ = lean_ctor_get(v_monadInfo_1993_, 4);
lean_inc_ref(v_cachedPUnitUnit_1999_);
lean_inc_ref(v_cachedPUnit_1998_);
lean_inc(v_v_1997_);
lean_inc(v_u_1996_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 4, v_cachedPUnitUnit_1999_);
lean_ctor_set(v___x_1990_, 3, v_cachedPUnit_1998_);
lean_ctor_set(v___x_1990_, 2, v_v_1997_);
lean_ctor_set(v___x_1990_, 1, v_u_1996_);
lean_ctor_set(v___x_1990_, 0, v_a_1994_);
v___x_2001_ = v___x_1990_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_1994_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_u_1996_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_cachedPUnit_1998_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_cachedPUnitUnit_1999_);
v___x_2001_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2001_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2005_ = 0;
v___x_2006_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2004_, v___x_2005_, v_a_1979_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___y_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
if (v_hasContinue_1978_ == 0)
{
v___y_2009_ = v_a_2007_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_2041_ = lean_box(0);
lean_inc(v_u_1996_);
v___x_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_u_1996_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_mkConst(v___x_2040_, v___x_2042_);
v___x_2044_ = l_Lean_Expr_app___override(v___x_2043_, v_a_2007_);
v___y_2009_ = v___x_2044_;
goto v___jp_2008_;
}
v___jp_2008_:
{
lean_object* v___x_2010_; 
lean_inc_ref(v_doBlockResultType_1995_);
v___x_2010_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_1995_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1));
v___x_2013_ = lean_box(0);
lean_inc(v_v_1997_);
v___x_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_v_1997_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
lean_inc(v_u_1996_);
v___x_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_u_1996_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = l_Lean_mkConst(v___x_2012_, v___x_2015_);
v___x_2017_ = l_Lean_mkApp3(v___x_2016_, v___y_2009_, v_a_1994_, v_a_2003_);
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1984_);
lean_inc(v_a_1983_);
lean_inc_ref(v_a_1982_);
lean_inc(v_a_1981_);
lean_inc_ref(v_a_1980_);
lean_inc_ref(v_a_1979_);
v___x_2018_ = lean_apply_9(v_runInBase_1988_, v___x_2017_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, lean_box(0));
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc_n(v_a_2019_, 2);
lean_dec_ref_known(v___x_2018_, 1);
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1984_);
lean_inc(v_a_1983_);
lean_inc_ref(v_a_1982_);
v___x_2020_ = lean_infer_type(v_a_2019_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2));
v___x_2023_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2022_, v_a_2011_, v_a_2021_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_2023_, 0);
lean_dec(v_unused_2031_);
v___x_2025_ = v___x_2023_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v___x_2023_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v_a_2019_);
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2019_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_2019_);
v_a_2032_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2023_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2023_);
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
lean_dec(v_a_2019_);
lean_dec(v_a_2011_);
return v___x_2020_;
}
}
else
{
lean_dec(v_a_2011_);
return v___x_2018_;
}
}
else
{
lean_dec_ref(v___y_2009_);
lean_dec(v_a_2003_);
lean_dec(v_a_1994_);
lean_dec_ref(v_runInBase_1988_);
return v___x_2010_;
}
}
}
else
{
lean_dec(v_a_2003_);
lean_dec(v_a_1994_);
lean_dec_ref(v_runInBase_1988_);
return v___x_2006_;
}
}
else
{
lean_dec(v_a_1994_);
lean_dec_ref(v_runInBase_1988_);
return v___x_2002_;
}
}
}
else
{
lean_del_object(v___x_1990_);
lean_dec_ref(v_runInBase_1988_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object* v_base_2050_, lean_object* v_hasContinue_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
uint8_t v_hasContinue_boxed_2060_; lean_object* v_res_2061_; 
v_hasContinue_boxed_2060_ = lean_unbox(v_hasContinue_2051_);
v_res_2061_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2050_, v_hasContinue_boxed_2060_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object* v_base_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_m_2076_; lean_object* v_runInBase_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2128_; 
v_m_2076_ = lean_ctor_get(v_base_2067_, 1);
v_runInBase_2077_ = lean_ctor_get(v_base_2067_, 3);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_base_2067_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; 
v_unused_2129_ = lean_ctor_get(v_base_2067_, 4);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_base_2067_, 2);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_base_2067_, 0);
lean_dec(v_unused_2131_);
v___x_2079_ = v_base_2067_;
v_isShared_2080_ = v_isSharedCheck_2128_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_runInBase_2077_);
lean_inc(v_m_2076_);
lean_dec(v_base_2067_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2128_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; 
lean_inc(v_a_2074_);
lean_inc_ref(v_a_2073_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc_ref(v_a_2068_);
v___x_2081_ = lean_apply_8(v_m_2076_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, lean_box(0));
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_monadInfo_2082_; lean_object* v_a_2083_; lean_object* v_doBlockResultType_2084_; lean_object* v_u_2085_; lean_object* v_v_2086_; lean_object* v_cachedPUnit_2087_; lean_object* v_cachedPUnitUnit_2088_; lean_object* v___x_2090_; 
v_monadInfo_2082_ = lean_ctor_get(v_a_2068_, 0);
v_a_2083_ = lean_ctor_get(v___x_2081_, 0);
lean_inc_n(v_a_2083_, 2);
lean_dec_ref_known(v___x_2081_, 1);
v_doBlockResultType_2084_ = lean_ctor_get(v_a_2068_, 3);
v_u_2085_ = lean_ctor_get(v_monadInfo_2082_, 1);
v_v_2086_ = lean_ctor_get(v_monadInfo_2082_, 2);
v_cachedPUnit_2087_ = lean_ctor_get(v_monadInfo_2082_, 3);
v_cachedPUnitUnit_2088_ = lean_ctor_get(v_monadInfo_2082_, 4);
lean_inc_ref(v_cachedPUnitUnit_2088_);
lean_inc_ref(v_cachedPUnit_2087_);
lean_inc(v_v_2086_);
lean_inc(v_u_2085_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 4, v_cachedPUnitUnit_2088_);
lean_ctor_set(v___x_2079_, 3, v_cachedPUnit_2087_);
lean_ctor_set(v___x_2079_, 2, v_v_2086_);
lean_ctor_set(v___x_2079_, 1, v_u_2085_);
lean_ctor_set(v___x_2079_, 0, v_a_2083_);
v___x_2090_ = v___x_2079_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2083_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_u_2085_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_v_2086_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_cachedPUnit_2087_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v_cachedPUnitUnit_2088_);
v___x_2090_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; 
v___x_2091_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2090_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2094_ = 0;
v___x_2095_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2093_, v___x_2094_, v_a_2068_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
lean_inc_ref(v_doBlockResultType_2084_);
v___x_2097_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2084_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1));
v___x_2100_ = lean_box(0);
lean_inc(v_v_2086_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_v_2086_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
lean_inc(v_u_2085_);
v___x_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_u_2085_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_mkConst(v___x_2099_, v___x_2102_);
v___x_2104_ = l_Lean_mkApp3(v___x_2103_, v_a_2096_, v_a_2083_, v_a_2092_);
lean_inc(v_a_2074_);
lean_inc_ref(v_a_2073_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc_ref(v_a_2068_);
v___x_2105_ = lean_apply_9(v_runInBase_2077_, v___x_2104_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, lean_box(0));
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_n(v_a_2106_, 2);
lean_dec_ref_known(v___x_2105_, 1);
lean_inc(v_a_2074_);
lean_inc_ref(v_a_2073_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
v___x_2107_ = lean_infer_type(v_a_2106_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2));
v___x_2110_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2109_, v_a_2098_, v_a_2108_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v___x_2110_, 0);
lean_dec(v_unused_2118_);
v___x_2112_ = v___x_2110_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_a_2106_);
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2106_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2106_);
v_a_2119_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2110_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2110_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_dec(v_a_2106_);
lean_dec(v_a_2098_);
return v___x_2107_;
}
}
else
{
lean_dec(v_a_2098_);
return v___x_2105_;
}
}
else
{
lean_dec(v_a_2096_);
lean_dec(v_a_2092_);
lean_dec(v_a_2083_);
lean_dec_ref(v_runInBase_2077_);
return v___x_2097_;
}
}
else
{
lean_dec(v_a_2092_);
lean_dec(v_a_2083_);
lean_dec_ref(v_runInBase_2077_);
return v___x_2095_;
}
}
else
{
lean_dec(v_a_2083_);
lean_dec_ref(v_runInBase_2077_);
return v___x_2091_;
}
}
}
else
{
lean_del_object(v___x_2079_);
lean_dec_ref(v_runInBase_2077_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object* v_base_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object* v_base_2150_, lean_object* v_r_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_m_2160_; lean_object* v_runInBase_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2207_; 
v_m_2160_ = lean_ctor_get(v_base_2150_, 1);
v_runInBase_2161_ = lean_ctor_get(v_base_2150_, 3);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_base_2150_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2208_ = lean_ctor_get(v_base_2150_, 4);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_base_2150_, 2);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_base_2150_, 0);
lean_dec(v_unused_2210_);
v___x_2163_ = v_base_2150_;
v_isShared_2164_ = v_isSharedCheck_2207_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_runInBase_2161_);
lean_inc(v_m_2160_);
lean_dec(v_base_2150_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2207_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; 
lean_inc(v_a_2158_);
lean_inc_ref(v_a_2157_);
lean_inc(v_a_2156_);
lean_inc_ref(v_a_2155_);
lean_inc(v_a_2154_);
lean_inc_ref(v_a_2153_);
lean_inc_ref(v_a_2152_);
v___x_2165_ = lean_apply_8(v_m_2160_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_monadInfo_2166_; lean_object* v_a_2167_; lean_object* v_doBlockResultType_2168_; lean_object* v_u_2169_; lean_object* v_v_2170_; lean_object* v_cachedPUnit_2171_; lean_object* v_cachedPUnitUnit_2172_; lean_object* v___x_2174_; 
v_monadInfo_2166_ = lean_ctor_get(v_a_2152_, 0);
v_a_2167_ = lean_ctor_get(v___x_2165_, 0);
lean_inc_n(v_a_2167_, 2);
lean_dec_ref_known(v___x_2165_, 1);
v_doBlockResultType_2168_ = lean_ctor_get(v_a_2152_, 3);
v_u_2169_ = lean_ctor_get(v_monadInfo_2166_, 1);
v_v_2170_ = lean_ctor_get(v_monadInfo_2166_, 2);
v_cachedPUnit_2171_ = lean_ctor_get(v_monadInfo_2166_, 3);
v_cachedPUnitUnit_2172_ = lean_ctor_get(v_monadInfo_2166_, 4);
lean_inc_ref(v_cachedPUnitUnit_2172_);
lean_inc_ref(v_cachedPUnit_2171_);
lean_inc(v_v_2170_);
lean_inc(v_u_2169_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 4, v_cachedPUnitUnit_2172_);
lean_ctor_set(v___x_2163_, 3, v_cachedPUnit_2171_);
lean_ctor_set(v___x_2163_, 2, v_v_2170_);
lean_ctor_set(v___x_2163_, 1, v_u_2169_);
lean_ctor_set(v___x_2163_, 0, v_a_2167_);
v___x_2174_ = v___x_2163_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2167_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_u_2169_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2170_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_cachedPUnit_2171_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_cachedPUnitUnit_2172_);
v___x_2174_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; 
v___x_2175_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2174_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
lean_inc(v_a_2158_);
lean_inc_ref(v_a_2157_);
lean_inc(v_a_2156_);
lean_inc_ref(v_a_2155_);
lean_inc_ref(v_r_2151_);
v___x_2177_ = lean_infer_type(v_r_2151_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1));
v___x_2180_ = 0;
v___x_2181_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2179_, v___x_2180_, v_a_2152_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
lean_inc_ref(v_doBlockResultType_2168_);
v___x_2183_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2168_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
v___x_2186_ = lean_box(0);
lean_inc(v_v_2170_);
v___x_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_v_2170_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
lean_inc(v_u_2169_);
v___x_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_u_2169_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_inc_ref(v___x_2188_);
v___x_2189_ = l_Lean_mkConst(v___x_2185_, v___x_2188_);
lean_inc(v_a_2182_);
lean_inc(v_a_2178_);
v___x_2190_ = l_Lean_mkAppB(v___x_2189_, v_a_2178_, v_a_2182_);
lean_inc(v_a_2167_);
v___x_2191_ = l_Lean_Expr_app___override(v_a_2167_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2));
v___x_2193_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2192_, v_a_2184_, v___x_2191_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref_known(v___x_2193_, 1);
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4));
v___x_2195_ = l_Lean_mkConst(v___x_2194_, v___x_2188_);
v___x_2196_ = l_Lean_mkApp5(v___x_2195_, v_a_2178_, v_a_2167_, v_a_2182_, v_a_2176_, v_r_2151_);
lean_inc(v_a_2158_);
lean_inc_ref(v_a_2157_);
lean_inc(v_a_2156_);
lean_inc_ref(v_a_2155_);
lean_inc(v_a_2154_);
lean_inc_ref(v_a_2153_);
lean_inc_ref(v_a_2152_);
v___x_2197_ = lean_apply_9(v_runInBase_2161_, v___x_2196_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, lean_box(0));
return v___x_2197_;
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref_known(v___x_2188_, 2);
lean_dec(v_a_2182_);
lean_dec(v_a_2178_);
lean_dec(v_a_2176_);
lean_dec(v_a_2167_);
lean_dec_ref(v_runInBase_2161_);
lean_dec_ref(v_r_2151_);
v_a_2198_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2193_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2193_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_dec(v_a_2182_);
lean_dec(v_a_2178_);
lean_dec(v_a_2176_);
lean_dec(v_a_2167_);
lean_dec_ref(v_runInBase_2161_);
lean_dec_ref(v_r_2151_);
return v___x_2183_;
}
}
else
{
lean_dec(v_a_2178_);
lean_dec(v_a_2176_);
lean_dec(v_a_2167_);
lean_dec_ref(v_runInBase_2161_);
lean_dec_ref(v_r_2151_);
return v___x_2181_;
}
}
else
{
lean_dec(v_a_2176_);
lean_dec(v_a_2167_);
lean_dec_ref(v_runInBase_2161_);
lean_dec_ref(v_r_2151_);
return v___x_2177_;
}
}
else
{
lean_dec(v_a_2167_);
lean_dec_ref(v_runInBase_2161_);
lean_dec_ref(v_r_2151_);
return v___x_2175_;
}
}
}
else
{
lean_del_object(v___x_2163_);
lean_dec_ref(v_runInBase_2161_);
lean_dec_ref(v_r_2151_);
return v___x_2165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object* v_base_2211_, lean_object* v_r_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2211_, v_r_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec_ref(v_a_2213_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object* v_base_2236_, lean_object* v_resultName_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_m_2246_; lean_object* v_runInBase_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2280_; 
v_m_2246_ = lean_ctor_get(v_base_2236_, 1);
v_runInBase_2247_ = lean_ctor_get(v_base_2236_, 3);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_base_2236_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; lean_object* v_unused_2282_; lean_object* v_unused_2283_; 
v_unused_2281_ = lean_ctor_get(v_base_2236_, 4);
lean_dec(v_unused_2281_);
v_unused_2282_ = lean_ctor_get(v_base_2236_, 2);
lean_dec(v_unused_2282_);
v_unused_2283_ = lean_ctor_get(v_base_2236_, 0);
lean_dec(v_unused_2283_);
v___x_2249_ = v_base_2236_;
v_isShared_2250_ = v_isSharedCheck_2280_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_runInBase_2247_);
lean_inc(v_m_2246_);
lean_dec(v_base_2236_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2280_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; 
lean_inc(v_a_2244_);
lean_inc_ref(v_a_2243_);
lean_inc(v_a_2242_);
lean_inc_ref(v_a_2241_);
lean_inc(v_a_2240_);
lean_inc_ref(v_a_2239_);
lean_inc_ref(v_a_2238_);
v___x_2251_ = lean_apply_8(v_m_2246_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, lean_box(0));
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_monadInfo_2252_; lean_object* v_a_2253_; lean_object* v_u_2254_; lean_object* v_v_2255_; lean_object* v_cachedPUnit_2256_; lean_object* v_cachedPUnitUnit_2257_; lean_object* v___x_2259_; 
v_monadInfo_2252_ = lean_ctor_get(v_a_2238_, 0);
v_a_2253_ = lean_ctor_get(v___x_2251_, 0);
lean_inc_n(v_a_2253_, 2);
lean_dec_ref_known(v___x_2251_, 1);
v_u_2254_ = lean_ctor_get(v_monadInfo_2252_, 1);
v_v_2255_ = lean_ctor_get(v_monadInfo_2252_, 2);
v_cachedPUnit_2256_ = lean_ctor_get(v_monadInfo_2252_, 3);
v_cachedPUnitUnit_2257_ = lean_ctor_get(v_monadInfo_2252_, 4);
lean_inc_ref(v_cachedPUnitUnit_2257_);
lean_inc_ref(v_cachedPUnit_2256_);
lean_inc(v_v_2255_);
lean_inc(v_u_2254_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 4, v_cachedPUnitUnit_2257_);
lean_ctor_set(v___x_2249_, 3, v_cachedPUnit_2256_);
lean_ctor_set(v___x_2249_, 2, v_v_2255_);
lean_ctor_set(v___x_2249_, 1, v_u_2254_);
lean_ctor_set(v___x_2249_, 0, v_a_2253_);
v___x_2259_ = v___x_2249_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2253_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_u_2254_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_v_2255_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_cachedPUnit_2256_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_cachedPUnitUnit_2257_);
v___x_2259_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2259_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = l_Lean_Meta_getFVarFromUserName(v_resultName_2237_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_n(v_a_2263_, 2);
lean_dec_ref_known(v___x_2262_, 1);
lean_inc(v_a_2244_);
lean_inc_ref(v_a_2243_);
lean_inc(v_a_2242_);
lean_inc_ref(v_a_2241_);
v___x_2264_ = lean_infer_type(v_a_2263_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__2));
v___x_2267_ = lean_box(0);
lean_inc(v_v_2255_);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_v_2255_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
lean_inc(v_u_2254_);
v___x_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_u_2254_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
lean_inc_ref_n(v___x_2269_, 2);
v___x_2270_ = l_Lean_mkConst(v___x_2266_, v___x_2269_);
v___x_2271_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__4));
v___x_2272_ = l_Lean_mkConst(v___x_2271_, v___x_2269_);
lean_inc_n(v_a_2253_, 2);
v___x_2273_ = l_Lean_mkAppB(v___x_2272_, v_a_2253_, v_a_2261_);
v___x_2274_ = l_Lean_mkAppB(v___x_2270_, v_a_2253_, v___x_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__7));
v___x_2276_ = l_Lean_mkConst(v___x_2275_, v___x_2269_);
v___x_2277_ = l_Lean_mkApp4(v___x_2276_, v_a_2253_, v___x_2274_, v_a_2265_, v_a_2263_);
lean_inc(v_a_2244_);
lean_inc_ref(v_a_2243_);
lean_inc(v_a_2242_);
lean_inc_ref(v_a_2241_);
lean_inc(v_a_2240_);
lean_inc_ref(v_a_2239_);
lean_inc_ref(v_a_2238_);
v___x_2278_ = lean_apply_9(v_runInBase_2247_, v___x_2277_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, lean_box(0));
return v___x_2278_;
}
else
{
lean_dec(v_a_2263_);
lean_dec(v_a_2261_);
lean_dec(v_a_2253_);
lean_dec_ref(v_runInBase_2247_);
return v___x_2264_;
}
}
else
{
lean_dec(v_a_2261_);
lean_dec(v_a_2253_);
lean_dec_ref(v_runInBase_2247_);
return v___x_2262_;
}
}
else
{
lean_dec(v_a_2253_);
lean_dec_ref(v_runInBase_2247_);
lean_dec(v_resultName_2237_);
return v___x_2260_;
}
}
}
else
{
lean_del_object(v___x_2249_);
lean_dec_ref(v_runInBase_2247_);
lean_dec(v_resultName_2237_);
return v___x_2251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object* v_base_2284_, lean_object* v_resultName_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2284_, v_resultName_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(lean_object* v_info_2295_, lean_object* v_as_2296_, size_t v_i_2297_, size_t v_stop_2298_, lean_object* v_b_2299_){
_start:
{
lean_object* v___y_2301_; uint8_t v___x_2305_; 
v___x_2305_ = lean_usize_dec_eq(v_i_2297_, v_stop_2298_);
if (v___x_2305_ == 0)
{
lean_object* v_reassigns_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_reassigns_2306_ = lean_ctor_get(v_info_2295_, 1);
v___x_2307_ = lean_array_uget_borrowed(v_as_2296_, v_i_2297_);
v___x_2308_ = l_Lean_Elab_Do_MutVar_getId(v___x_2307_);
v___x_2309_ = l_Lean_NameSet_contains(v_reassigns_2306_, v___x_2308_);
lean_dec(v___x_2308_);
if (v___x_2309_ == 0)
{
v___y_2301_ = v_b_2299_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2310_; 
lean_inc(v___x_2307_);
v___x_2310_ = lean_array_push(v_b_2299_, v___x_2307_);
v___y_2301_ = v___x_2310_;
goto v___jp_2300_;
}
}
else
{
return v_b_2299_;
}
v___jp_2300_:
{
size_t v___x_2302_; size_t v___x_2303_; 
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_add(v_i_2297_, v___x_2302_);
v_i_2297_ = v___x_2303_;
v_b_2299_ = v___y_2301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0___boxed(lean_object* v_info_2311_, lean_object* v_as_2312_, lean_object* v_i_2313_, lean_object* v_stop_2314_, lean_object* v_b_2315_){
_start:
{
size_t v_i_boxed_2316_; size_t v_stop_boxed_2317_; lean_object* v_res_2318_; 
v_i_boxed_2316_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_stop_boxed_2317_ = lean_unbox_usize(v_stop_2314_);
lean_dec(v_stop_2314_);
v_res_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2311_, v_as_2312_, v_i_boxed_2316_, v_stop_boxed_2317_, v_b_2315_);
lean_dec_ref(v_as_2312_);
lean_dec_ref(v_info_2311_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object* v_info_2321_, lean_object* v_dec_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v_continueBase_x3f_2334_; lean_object* v_controlStack_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v_monadInfo_2363_; lean_object* v_mutVars_2364_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v_breakBase_x3f_2369_; lean_object* v_controlStack_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2381_; lean_object* v___y_2382_; uint8_t v___y_2383_; uint8_t v___y_2384_; lean_object* v_controlStack_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; uint8_t v___y_2399_; lean_object* v_returnBase_x3f_2400_; lean_object* v_controlStack_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2414_; uint8_t v___y_2415_; uint8_t v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2430_; uint8_t v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; uint8_t v___y_2434_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v___y_2445_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2479_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_monadInfo_2363_ = lean_ctor_get(v_a_2323_, 0);
v_mutVars_2364_ = lean_ctor_get(v_a_2323_, 1);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_mutVars_2364_);
v___x_2522_ = ((lean_object*)(l_Lean_Elab_Do_EffectForwarder_ofCont___closed__0));
v___x_2523_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2523_ == 0)
{
v___y_2479_ = v___x_2522_;
goto v___jp_2478_;
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_nat_dec_le(v___x_2521_, v___x_2521_);
if (v___x_2524_ == 0)
{
if (v___x_2523_ == 0)
{
v___y_2479_ = v___x_2522_;
goto v___jp_2478_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2521_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2321_, v_mutVars_2364_, v___x_2525_, v___x_2526_, v___x_2522_);
v___y_2479_ = v___x_2527_;
goto v___jp_2478_;
}
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = lean_usize_of_nat(v___x_2521_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_EffectForwarder_ofCont_spec__0(v_info_2321_, v_mutVars_2364_, v___x_2528_, v___x_2529_, v___x_2522_);
v___y_2479_ = v___x_2530_;
goto v___jp_2478_;
}
}
v___jp_2331_:
{
lean_object* v_stM_2343_; lean_object* v_resultType_2344_; lean_object* v___x_2345_; 
v_stM_2343_ = lean_ctor_get(v_controlStack_2335_, 2);
v_resultType_2344_ = lean_ctor_get(v_dec_2322_, 1);
lean_inc_ref(v_stM_2343_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc_ref(v_resultType_2344_);
v___x_2345_ = lean_apply_9(v_stM_2343_, v_resultType_2344_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, lean_box(0));
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2354_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2354_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2354_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2350_, 0, v_dec_2322_);
lean_ctor_set(v___x_2350_, 1, v___y_2333_);
lean_ctor_set(v___x_2350_, 2, v___y_2332_);
lean_ctor_set(v___x_2350_, 3, v_continueBase_x3f_2334_);
lean_ctor_set(v___x_2350_, 4, v_controlStack_2335_);
lean_ctor_set(v___x_2350_, 5, v_a_2346_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_controlStack_2335_);
lean_dec(v_continueBase_x3f_2334_);
lean_dec(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v_dec_2322_);
v_a_2355_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2345_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2345_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
v___jp_2365_:
{
if (v___y_2368_ == 0)
{
v___y_2332_ = v_breakBase_x3f_2369_;
v___y_2333_ = v___y_2366_;
v_continueBase_x3f_2334_ = v___y_2367_;
v_controlStack_2335_ = v_controlStack_2370_;
v___y_2336_ = v___y_2371_;
v___y_2337_ = v___y_2372_;
v___y_2338_ = v___y_2373_;
v___y_2339_ = v___y_2374_;
v___y_2340_ = v___y_2375_;
v___y_2341_ = v___y_2376_;
v___y_2342_ = v___y_2377_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec(v___y_2367_);
lean_inc_ref(v_controlStack_2370_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_controlStack_2370_);
lean_inc_ref(v_monadInfo_2363_);
v___x_2379_ = l_Lean_Elab_Do_ControlStack_continueT(v_monadInfo_2363_, v_controlStack_2370_);
v___y_2332_ = v_breakBase_x3f_2369_;
v___y_2333_ = v___y_2366_;
v_continueBase_x3f_2334_ = v___x_2378_;
v_controlStack_2335_ = v___x_2379_;
v___y_2336_ = v___y_2371_;
v___y_2337_ = v___y_2372_;
v___y_2338_ = v___y_2373_;
v___y_2339_ = v___y_2374_;
v___y_2340_ = v___y_2375_;
v___y_2341_ = v___y_2376_;
v___y_2342_ = v___y_2377_;
goto v___jp_2331_;
}
}
v___jp_2380_:
{
if (v___y_2383_ == 0)
{
lean_inc(v___y_2382_);
v___y_2366_ = v___y_2381_;
v___y_2367_ = v___y_2382_;
v___y_2368_ = v___y_2384_;
v_breakBase_x3f_2369_ = v___y_2382_;
v_controlStack_2370_ = v_controlStack_2385_;
v___y_2371_ = v___y_2386_;
v___y_2372_ = v___y_2387_;
v___y_2373_ = v___y_2388_;
v___y_2374_ = v___y_2389_;
v___y_2375_ = v___y_2390_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2392_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_inc_ref(v_controlStack_2385_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_controlStack_2385_);
lean_inc_ref(v_monadInfo_2363_);
v___x_2394_ = l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_2363_, v_controlStack_2385_);
v___y_2366_ = v___y_2381_;
v___y_2367_ = v___y_2382_;
v___y_2368_ = v___y_2384_;
v_breakBase_x3f_2369_ = v___x_2393_;
v_controlStack_2370_ = v___x_2394_;
v___y_2371_ = v___y_2386_;
v___y_2372_ = v___y_2387_;
v___y_2373_ = v___y_2388_;
v___y_2374_ = v___y_2389_;
v___y_2375_ = v___y_2390_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2392_;
goto v___jp_2365_;
}
}
v___jp_2395_:
{
if (lean_obj_tag(v___y_2397_) == 1)
{
lean_object* v_val_2409_; lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v___x_2412_; 
v_val_2409_ = lean_ctor_get(v___y_2397_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v___y_2397_, 1);
v_fst_2410_ = lean_ctor_get(v_val_2409_, 0);
lean_inc(v_fst_2410_);
v_snd_2411_ = lean_ctor_get(v_val_2409_, 1);
lean_inc(v_snd_2411_);
lean_dec(v_val_2409_);
lean_inc_ref(v_monadInfo_2363_);
v___x_2412_ = l_Lean_Elab_Do_ControlStack_stateT(v_monadInfo_2363_, v_fst_2410_, v_snd_2411_, v_controlStack_2401_);
v___y_2381_ = v_returnBase_x3f_2400_;
v___y_2382_ = v___y_2396_;
v___y_2383_ = v___y_2398_;
v___y_2384_ = v___y_2399_;
v_controlStack_2385_ = v___x_2412_;
v___y_2386_ = v___y_2402_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v___y_2404_;
v___y_2389_ = v___y_2405_;
v___y_2390_ = v___y_2406_;
v___y_2391_ = v___y_2407_;
v___y_2392_ = v___y_2408_;
goto v___jp_2380_;
}
else
{
lean_dec(v___y_2397_);
v___y_2381_ = v_returnBase_x3f_2400_;
v___y_2382_ = v___y_2396_;
v___y_2383_ = v___y_2398_;
v___y_2384_ = v___y_2399_;
v_controlStack_2385_ = v_controlStack_2401_;
v___y_2386_ = v___y_2402_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v___y_2404_;
v___y_2389_ = v___y_2405_;
v___y_2390_ = v___y_2406_;
v___y_2391_ = v___y_2407_;
v___y_2392_ = v___y_2408_;
goto v___jp_2380_;
}
}
v___jp_2413_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_box(0);
lean_inc_ref(v_monadInfo_2363_);
v___x_2419_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_2363_);
if (lean_obj_tag(v___y_2414_) == 1)
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2428_; 
v_val_2420_ = lean_ctor_get(v___y_2414_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___y_2414_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2422_ = v___y_2414_;
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v___y_2414_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
lean_inc_ref(v___x_2419_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2419_);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2419_);
v___x_2425_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; 
lean_inc_ref(v_monadInfo_2363_);
v___x_2426_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(v_monadInfo_2363_, v_val_2420_, v___x_2419_);
v___y_2396_ = v___x_2418_;
v___y_2397_ = v___y_2417_;
v___y_2398_ = v___y_2415_;
v___y_2399_ = v___y_2416_;
v_returnBase_x3f_2400_ = v___x_2425_;
v_controlStack_2401_ = v___x_2426_;
v___y_2402_ = v_a_2323_;
v___y_2403_ = v_a_2324_;
v___y_2404_ = v_a_2325_;
v___y_2405_ = v_a_2326_;
v___y_2406_ = v_a_2327_;
v___y_2407_ = v_a_2328_;
v___y_2408_ = v_a_2329_;
goto v___jp_2395_;
}
}
}
else
{
lean_dec(v___y_2414_);
v___y_2396_ = v___x_2418_;
v___y_2397_ = v___y_2417_;
v___y_2398_ = v___y_2415_;
v___y_2399_ = v___y_2416_;
v_returnBase_x3f_2400_ = v___x_2418_;
v_controlStack_2401_ = v___x_2419_;
v___y_2402_ = v_a_2323_;
v___y_2403_ = v_a_2324_;
v___y_2404_ = v_a_2325_;
v___y_2405_ = v_a_2326_;
v___y_2406_ = v_a_2327_;
v___y_2407_ = v_a_2328_;
v___y_2408_ = v_a_2329_;
goto v___jp_2395_;
}
}
v___jp_2429_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2435_ = lean_array_get_size(v___y_2433_);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_nat_dec_eq(v___x_2435_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___y_2433_);
lean_ctor_set(v___x_2438_, 1, v___y_2430_);
v___x_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
v___y_2414_ = v___y_2432_;
v___y_2415_ = v___y_2431_;
v___y_2416_ = v___y_2434_;
v___y_2417_ = v___x_2439_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2440_; 
lean_dec_ref(v___y_2433_);
lean_dec_ref(v___y_2430_);
v___x_2440_ = lean_box(0);
v___y_2414_ = v___y_2432_;
v___y_2415_ = v___y_2431_;
v___y_2416_ = v___y_2434_;
v___y_2417_ = v___x_2440_;
goto v___jp_2413_;
}
}
v___jp_2441_:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2323_);
if (lean_obj_tag(v___x_2446_) == 0)
{
uint8_t v_continues_2447_; 
v_continues_2447_ = lean_ctor_get_uint8(v_info_2321_, sizeof(void*)*2 + 1);
if (v_continues_2447_ == 0)
{
lean_dec_ref_known(v___x_2446_, 1);
v___y_2430_ = v___y_2442_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2443_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v_continues_2447_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2448_; 
v_a_2448_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2446_, 1);
if (lean_obj_tag(v_a_2448_) == 0)
{
uint8_t v___x_2449_; 
v___x_2449_ = 0;
v___y_2430_ = v___y_2442_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2443_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___x_2449_;
goto v___jp_2429_;
}
else
{
lean_dec_ref_known(v_a_2448_, 1);
v___y_2430_ = v___y_2442_;
v___y_2431_ = v___y_2445_;
v___y_2432_ = v___y_2443_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v_continues_2447_;
goto v___jp_2429_;
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v_dec_2322_);
v_a_2450_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2446_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2446_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
v___jp_2458_:
{
uint8_t v___x_2462_; 
v___x_2462_ = 0;
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___y_2460_;
v___y_2444_ = v___y_2461_;
v___y_2445_ = v___x_2462_;
goto v___jp_2441_;
}
v___jp_2463_:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2323_);
if (lean_obj_tag(v___x_2467_) == 0)
{
uint8_t v_breaks_2468_; 
v_breaks_2468_ = lean_ctor_get_uint8(v_info_2321_, sizeof(void*)*2);
if (v_breaks_2468_ == 0)
{
lean_dec_ref_known(v___x_2467_, 1);
v___y_2459_ = v___y_2464_;
v___y_2460_ = v___y_2466_;
v___y_2461_ = v___y_2465_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2467_, 1);
if (lean_obj_tag(v_a_2469_) == 0)
{
v___y_2459_ = v___y_2464_;
v___y_2460_ = v___y_2466_;
v___y_2461_ = v___y_2465_;
goto v___jp_2458_;
}
else
{
lean_dec_ref_known(v_a_2469_, 1);
v___y_2442_ = v___y_2464_;
v___y_2443_ = v___y_2466_;
v___y_2444_ = v___y_2465_;
v___y_2445_ = v_breaks_2468_;
goto v___jp_2441_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_dec_2322_);
v_a_2470_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2467_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2467_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
v___jp_2478_:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2323_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; size_t v_sz_2482_; size_t v___x_2483_; lean_object* v___x_2484_; size_t v_sz_2485_; lean_object* v___x_2486_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v_sz_2482_ = lean_array_size(v___y_2479_);
v___x_2483_ = ((size_t)0ULL);
lean_inc_ref(v___y_2479_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_2482_, v___x_2483_, v___y_2479_);
v_sz_2485_ = lean_array_size(v___x_2484_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_2485_, v___x_2483_, v___x_2484_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v_u_2488_; lean_object* v___x_2489_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v_u_2488_ = lean_ctor_get(v_monadInfo_2363_, 1);
lean_inc(v_u_2488_);
v___x_2489_ = l_Lean_Meta_mkProdN(v_a_2487_, v_u_2488_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2489_) == 0)
{
uint8_t v_returnsEarly_2490_; 
v_returnsEarly_2490_ = lean_ctor_get_uint8(v_info_2321_, sizeof(void*)*2 + 2);
if (v_returnsEarly_2490_ == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2492_; 
lean_dec(v_a_2481_);
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2492_ = lean_box(0);
v___y_2464_ = v_a_2491_;
v___y_2465_ = v___y_2479_;
v___y_2466_ = v___x_2492_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2493_; lean_object* v_resultType_2494_; lean_object* v___x_2495_; 
v_a_2493_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2489_, 1);
v_resultType_2494_ = lean_ctor_get(v_a_2481_, 0);
lean_inc_ref(v_resultType_2494_);
lean_dec(v_a_2481_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_resultType_2494_);
v___y_2464_ = v_a_2493_;
v___y_2465_ = v___y_2479_;
v___y_2466_ = v___x_2495_;
goto v___jp_2463_;
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2481_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_dec_2322_);
v_a_2496_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2489_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2489_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_a_2481_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_dec_2322_);
v_a_2504_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2486_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2486_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_dec_2322_);
v_a_2512_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2480_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2480_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont___boxed(lean_object* v_info_2531_, lean_object* v_dec_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_info_2531_, v_dec_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec_ref(v_info_2531_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object* v_l_2542_, lean_object* v_elabElem_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2544_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2544_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2544_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2602_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
if (lean_obj_tag(v_a_2553_) == 1)
{
lean_object* v_breakBase_x3f_2613_; 
v_breakBase_x3f_2613_ = lean_ctor_get(v_l_2542_, 2);
lean_inc(v_breakBase_x3f_2613_);
if (lean_obj_tag(v_breakBase_x3f_2613_) == 1)
{
lean_object* v_continueBase_x3f_2614_; lean_object* v_val_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref_known(v_a_2553_, 1);
v_continueBase_x3f_2614_ = lean_ctor_get(v_l_2542_, 3);
v_val_2615_ = lean_ctor_get(v_breakBase_x3f_2613_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_breakBase_x3f_2613_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2617_ = v_breakBase_x3f_2613_;
v_isShared_2618_ = v_isSharedCheck_2628_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_val_2615_);
lean_dec(v_breakBase_x3f_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2628_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
uint8_t v___y_2620_; 
if (lean_obj_tag(v_continueBase_x3f_2614_) == 0)
{
uint8_t v___x_2626_; 
v___x_2626_ = 0;
v___y_2620_ = v___x_2626_;
goto v___jp_2619_;
}
else
{
uint8_t v___x_2627_; 
v___x_2627_ = 1;
v___y_2620_ = v___x_2627_;
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = lean_box(v___y_2620_);
v___x_2622_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkBreak___boxed), 10, 2);
lean_closure_set(v___x_2622_, 0, v_val_2615_);
lean_closure_set(v___x_2622_, 1, v___x_2621_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2622_);
v___x_2624_ = v___x_2617_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2602_ = v___x_2624_;
goto v___jp_2601_;
}
}
}
}
else
{
lean_dec(v_breakBase_x3f_2613_);
v___y_2602_ = v_a_2553_;
goto v___jp_2601_;
}
}
else
{
v___y_2602_ = v_a_2553_;
goto v___jp_2601_;
}
v___jp_2558_:
{
lean_object* v_origCont_2562_; lean_object* v_liftedStack_2563_; lean_object* v_liftedDoBlockResultType_2564_; lean_object* v_resultName_2565_; lean_object* v_resultType_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2584_; 
v_origCont_2562_ = lean_ctor_get(v_l_2542_, 0);
lean_inc_ref(v_origCont_2562_);
v_liftedStack_2563_ = lean_ctor_get(v_l_2542_, 4);
lean_inc_ref(v_liftedStack_2563_);
v_liftedDoBlockResultType_2564_ = lean_ctor_get(v_l_2542_, 5);
lean_inc_ref(v_liftedDoBlockResultType_2564_);
lean_dec_ref(v_l_2542_);
v_resultName_2565_ = lean_ctor_get(v_origCont_2562_, 0);
v_resultType_2566_ = lean_ctor_get(v_origCont_2562_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_origCont_2562_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v_origCont_2562_, 2);
lean_dec(v_unused_2585_);
v___x_2568_ = v_origCont_2562_;
v_isShared_2569_ = v_isSharedCheck_2584_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_resultType_2566_);
lean_inc(v_resultName_2565_);
lean_dec(v_origCont_2562_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2584_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_monadInfo_2570_; lean_object* v_mutVars_2571_; lean_object* v_mutVarDefs_2572_; uint8_t v_deadCode_2573_; lean_object* v_ops_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2580_; 
v_monadInfo_2570_ = lean_ctor_get(v_a_2544_, 0);
v_mutVars_2571_ = lean_ctor_get(v_a_2544_, 1);
v_mutVarDefs_2572_ = lean_ctor_get(v_a_2544_, 2);
v_deadCode_2573_ = lean_ctor_get_uint8(v_a_2544_, sizeof(void*)*6);
v_ops_2574_ = lean_ctor_get(v_a_2544_, 5);
lean_inc(v_resultName_2565_);
v___x_2575_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkPure___boxed), 10, 2);
lean_closure_set(v___x_2575_, 0, v_liftedStack_2563_);
lean_closure_set(v___x_2575_, 1, v_resultName_2565_);
v___x_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2561_);
lean_ctor_set(v___x_2576_, 1, v___y_2559_);
lean_ctor_set(v___x_2576_, 2, v___y_2560_);
v___x_2577_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_2576_);
lean_dec_ref_known(v___x_2576_, 3);
v___x_2578_ = 1;
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 2, v___x_2575_);
v___x_2580_ = v___x_2568_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_resultName_2565_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_resultType_2566_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v___x_2575_);
v___x_2580_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*3, v___x_2578_);
lean_inc(v_ops_2574_);
lean_inc_ref(v_mutVarDefs_2572_);
lean_inc_ref(v_mutVars_2571_);
lean_inc_ref(v_monadInfo_2570_);
v___x_2581_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2581_, 0, v_monadInfo_2570_);
lean_ctor_set(v___x_2581_, 1, v_mutVars_2571_);
lean_ctor_set(v___x_2581_, 2, v_mutVarDefs_2572_);
lean_ctor_set(v___x_2581_, 3, v_liftedDoBlockResultType_2564_);
lean_ctor_set(v___x_2581_, 4, v___x_2577_);
lean_ctor_set(v___x_2581_, 5, v_ops_2574_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*6, v_deadCode_2573_);
lean_inc(v_a_2550_);
lean_inc_ref(v_a_2549_);
lean_inc(v_a_2548_);
lean_inc_ref(v_a_2547_);
lean_inc(v_a_2546_);
lean_inc_ref(v_a_2545_);
v___x_2582_ = lean_apply_9(v_elabElem_2543_, v___x_2580_, v___x_2581_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, lean_box(0));
return v___x_2582_;
}
}
}
v___jp_2586_:
{
lean_object* v_returnBase_x3f_2589_; 
v_returnBase_x3f_2589_ = lean_ctor_get(v_l_2542_, 1);
if (lean_obj_tag(v_returnBase_x3f_2589_) == 1)
{
lean_object* v_val_2590_; lean_object* v_resultType_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2599_; 
v_val_2590_ = lean_ctor_get(v_returnBase_x3f_2589_, 0);
v_resultType_2591_ = lean_ctor_get(v_a_2557_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_a_2557_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v_a_2557_, 1);
lean_dec(v_unused_2600_);
v___x_2593_ = v_a_2557_;
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_resultType_2591_);
lean_dec(v_a_2557_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_inc(v_val_2590_);
v___x_2595_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkReturn___boxed), 10, 1);
lean_closure_set(v___x_2595_, 0, v_val_2590_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_resultType_2591_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
v___y_2559_ = v___y_2587_;
v___y_2560_ = v___y_2588_;
v___y_2561_ = v___x_2597_;
goto v___jp_2558_;
}
}
}
else
{
v___y_2559_ = v___y_2587_;
v___y_2560_ = v___y_2588_;
v___y_2561_ = v_a_2557_;
goto v___jp_2558_;
}
}
v___jp_2601_:
{
if (lean_obj_tag(v_a_2555_) == 1)
{
lean_object* v_continueBase_x3f_2603_; 
v_continueBase_x3f_2603_ = lean_ctor_get(v_l_2542_, 3);
lean_inc(v_continueBase_x3f_2603_);
if (lean_obj_tag(v_continueBase_x3f_2603_) == 1)
{
lean_object* v_val_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref_known(v_a_2555_, 1);
v_val_2604_ = lean_ctor_get(v_continueBase_x3f_2603_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_continueBase_x3f_2603_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v_continueBase_x3f_2603_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_val_2604_);
lean_dec(v_continueBase_x3f_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkContinue___boxed), 9, 1);
lean_closure_set(v___x_2608_, 0, v_val_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
v___y_2587_ = v___y_2602_;
v___y_2588_ = v___x_2610_;
goto v___jp_2586_;
}
}
}
else
{
lean_dec(v_continueBase_x3f_2603_);
v___y_2587_ = v___y_2602_;
v___y_2588_ = v_a_2555_;
goto v___jp_2586_;
}
}
else
{
v___y_2587_ = v___y_2602_;
v___y_2588_ = v_a_2555_;
goto v___jp_2586_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_a_2555_);
lean_dec(v_a_2553_);
lean_dec_ref(v_elabElem_2543_);
lean_dec_ref(v_l_2542_);
v_a_2629_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2556_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2556_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_a_2553_);
lean_dec_ref(v_elabElem_2543_);
lean_dec_ref(v_l_2542_);
v_a_2637_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2554_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2554_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v_elabElem_2543_);
lean_dec_ref(v_l_2542_);
v_a_2645_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2552_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2552_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_lift___boxed(lean_object* v_l_2653_, lean_object* v_elabElem_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_Elab_Do_EffectForwarder_lift(v_l_2653_, v_elabElem_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec_ref(v_a_2655_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object* v_l_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_liftedStack_2673_; lean_object* v_origCont_2674_; lean_object* v_restoreCont_2675_; lean_object* v___x_2676_; 
v_liftedStack_2673_ = lean_ctor_get(v_l_2664_, 4);
lean_inc_ref(v_liftedStack_2673_);
v_origCont_2674_ = lean_ctor_get(v_l_2664_, 0);
lean_inc_ref(v_origCont_2674_);
lean_dec_ref(v_l_2664_);
v_restoreCont_2675_ = lean_ctor_get(v_liftedStack_2673_, 4);
lean_inc_ref(v_restoreCont_2675_);
lean_dec_ref(v_liftedStack_2673_);
lean_inc(v_a_2671_);
lean_inc_ref(v_a_2670_);
lean_inc(v_a_2669_);
lean_inc_ref(v_a_2668_);
lean_inc(v_a_2667_);
lean_inc_ref(v_a_2666_);
lean_inc_ref(v_a_2665_);
v___x_2676_ = lean_apply_9(v_restoreCont_2675_, v_origCont_2674_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, lean_box(0));
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont___boxed(lean_object* v_l_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_l_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2686_;
}
}
lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_Control(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
