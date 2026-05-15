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
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getContinueCont___redArg(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getBreakCont___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_mkProdN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Do_bindMutVarsFromTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Do_withDeadCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Do_ControlLifter_ofCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_ControlLifter_ofCont___closed__0 = (const lean_object*)&l_Lean_Elab_Do_ControlLifter_ofCont___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_ofCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_restoreCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_restoreCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_71_);
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
lean_dec_ref(v___x_74_);
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
v___x_239_ = l_Lean_TSyntax_getId(v_v_236_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(lean_object* v_mutVarIdents_250_){
_start:
{
size_t v_sz_251_; size_t v___x_252_; lean_object* v___x_253_; 
v_sz_251_ = lean_array_size(v_mutVarIdents_250_);
v___x_252_ = ((size_t)0ULL);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_251_, v___x_252_, v_mutVarIdents_250_);
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
lean_dec_ref(v___x_265_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(lean_object* v_baseMonadInfo_293_, lean_object* v_mutVarIdents_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; size_t v_sz_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_303_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_mutVarIdents_294_);
v_sz_304_ = lean_array_size(v___x_303_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_304_, v___x_305_, v___x_303_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_u_308_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_306_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3___boxed(lean_object* v_baseMonadInfo_318_, lean_object* v_mutVarIdents_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_318_, v_mutVarIdents_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(lean_object* v_baseMonadInfo_358_, lean_object* v_mutVarIdents_359_, lean_object* v_00_u03b1_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
lean_inc_ref(v_baseMonadInfo_358_);
v___x_369_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_358_, v_mutVarIdents_359_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___boxed(lean_object* v_baseMonadInfo_385_, lean_object* v_mutVarIdents_386_, lean_object* v_00_u03b1_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_385_, v_mutVarIdents_386_, v_00_u03b1_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1(lean_object* v_baseMonadInfo_415_, lean_object* v_mutVarIdents_416_, lean_object* v_base_417_, lean_object* v_00_u03b1_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_415_, v_mutVarIdents_416_, v_00_u03b1_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_stM_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref(v___x_427_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(lean_object* v_baseMonadInfo_431_, lean_object* v_mutVarIdents_432_, lean_object* v_base_433_, lean_object* v_00_u03b1_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(v_baseMonadInfo_431_, v_mutVarIdents_432_, v_base_433_, v_00_u03b1_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2(lean_object* v_a_444_, lean_object* v_mutVarIdents_445_, lean_object* v_resultName_446_, lean_object* v_k_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_getFVarFromUserName(v_a_444_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_mutVarIdents_445_);
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
lean_dec_ref(v_mutVarIdents_445_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed(lean_object* v_a_463_, lean_object* v_mutVarIdents_464_, lean_object* v_resultName_465_, lean_object* v_k_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_Do_ControlStack_stateT___lam__2(v_a_463_, v_mutVarIdents_464_, v_resultName_465_, v_k_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3(lean_object* v_baseMonadInfo_479_, lean_object* v_mutVarIdents_480_, lean_object* v_base_481_, lean_object* v_dec_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
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
lean_dec_ref(v___x_492_);
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
lean_inc_ref(v_mutVarIdents_480_);
v___x_500_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(v_baseMonadInfo_479_, v_mutVarIdents_480_, v_resultType_495_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_restoreCont_502_; lean_object* v___f_503_; uint8_t v___x_504_; lean_object* v___x_506_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v_restoreCont_502_ = lean_ctor_get(v_base_481_, 4);
lean_inc_ref(v_restoreCont_502_);
lean_dec_ref(v_base_481_);
lean_inc(v_a_493_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed), 12, 4);
lean_closure_set(v___f_503_, 0, v_a_493_);
lean_closure_set(v___f_503_, 1, v_mutVarIdents_480_);
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
lean_dec_ref(v_mutVarIdents_480_);
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
lean_dec_ref(v_mutVarIdents_480_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(lean_object* v_baseMonadInfo_526_, lean_object* v_mutVarIdents_527_, lean_object* v_base_528_, lean_object* v_dec_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(v_baseMonadInfo_526_, v_mutVarIdents_527_, v_base_528_, v_dec_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
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
v___x_552_ = l_Lean_Syntax_getId(v_v_551_);
v___x_553_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_552_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = l_Lean_LocalDecl_toExpr(v_a_554_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_box(0);
v___x_558_ = 0;
lean_inc_ref(v___x_555_);
lean_inc(v_v_551_);
v___x_559_ = l_Lean_Elab_Term_addTermInfo_x27(v_v_551_, v___x_555_, v___x_556_, v___x_556_, v___x_557_, v___x_558_, v___x_558_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v___x_560_; lean_object* v_bs_x27_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v___x_559_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_bs_x27_561_ = lean_array_uset(v_bs_541_, v_i_540_, v___x_560_);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_540_, v___x_562_);
v___x_564_ = lean_array_uset(v_bs_x27_561_, v_i_540_, v___x_555_);
v_i_540_ = v___x_563_;
v_bs_541_ = v___x_564_;
goto _start;
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v___x_555_);
lean_dec_ref(v_bs_541_);
v_a_566_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_559_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_559_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_bs_541_);
v_a_574_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_553_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_553_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(lean_object* v_sz_582_, lean_object* v_i_583_, lean_object* v_bs_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_582_);
lean_dec(v_sz_582_);
v_i_boxed_593_ = lean_unbox_usize(v_i_583_);
lean_dec(v_i_583_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_592_, v_i_boxed_593_, v_bs_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0));
v___x_597_ = l_Lean_stringToMessageData(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4));
v___x_603_ = l_Lean_stringToMessageData(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4(lean_object* v_mutVarIdents_604_, lean_object* v_baseMonadInfo_605_, lean_object* v_00_u03c3_606_, lean_object* v_base_607_, lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
size_t v_sz_617_; size_t v___x_618_; lean_object* v___x_619_; 
v_sz_617_ = lean_array_size(v_mutVarIdents_604_);
v___x_618_ = ((size_t)0ULL);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_617_, v___x_618_, v_mutVarIdents_604_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_u_621_; lean_object* v___x_622_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___x_619_);
v_u_621_ = lean_ctor_get(v_baseMonadInfo_605_, 1);
lean_inc(v_u_621_);
lean_dec_ref(v_baseMonadInfo_605_);
v___x_622_ = l_Lean_Meta_mkProdMkN(v_a_620_, v_u_621_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_671_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_622_);
v_fst_624_ = lean_ctor_get(v_a_623_, 0);
v_snd_625_ = lean_ctor_get(v_a_623_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_671_ == 0)
{
v___x_627_ = v_a_623_;
v_isShared_628_ = v_isSharedCheck_671_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_625_);
lean_inc(v_fst_624_);
lean_dec(v_a_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_671_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___x_640_; 
lean_inc_ref(v_00_u03c3_606_);
lean_inc(v_snd_625_);
v___x_640_ = l_Lean_Meta_isExprDefEq(v_snd_625_, v_00_u03c3_606_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; uint8_t v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_unbox(v_a_641_);
lean_dec(v_a_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
lean_dec(v_fst_624_);
lean_dec_ref(v_e_608_);
lean_dec_ref(v_base_607_);
v___x_643_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1);
v___x_644_ = l_Lean_MessageData_ofExpr(v_00_u03c3_606_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 7);
lean_ctor_set(v___x_627_, 1, v___x_644_);
lean_ctor_set(v___x_627_, 0, v___x_643_);
v___x_646_ = v___x_627_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_662_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v___x_647_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_MessageData_ofExpr(v_snd_625_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5, &l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once, _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_652_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_del_object(v___x_627_);
lean_dec(v_snd_625_);
lean_dec_ref(v_00_u03c3_606_);
v___y_630_ = v___y_609_;
v___y_631_ = v___y_610_;
v___y_632_ = v___y_611_;
v___y_633_ = v___y_612_;
v___y_634_ = v___y_613_;
v___y_635_ = v___y_614_;
v___y_636_ = v___y_615_;
goto v___jp_629_;
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_del_object(v___x_627_);
lean_dec(v_snd_625_);
lean_dec(v_fst_624_);
lean_dec_ref(v_e_608_);
lean_dec_ref(v_base_607_);
lean_dec_ref(v_00_u03c3_606_);
v_a_663_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_640_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_640_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
v___jp_629_:
{
lean_object* v_runInBase_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_runInBase_637_ = lean_ctor_get(v_base_607_, 3);
lean_inc_ref(v_runInBase_637_);
lean_dec_ref(v_base_607_);
v___x_638_ = l_Lean_Expr_app___override(v_e_608_, v_fst_624_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_632_);
lean_inc_ref(v___y_631_);
lean_inc_ref(v___y_630_);
v___x_639_ = lean_apply_9(v_runInBase_637_, v___x_638_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, lean_box(0));
return v___x_639_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_e_608_);
lean_dec_ref(v_base_607_);
lean_dec_ref(v_00_u03c3_606_);
v_a_672_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_622_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_622_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_e_608_);
lean_dec_ref(v_base_607_);
lean_dec_ref(v_00_u03c3_606_);
lean_dec_ref(v_baseMonadInfo_605_);
v_a_680_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_619_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_619_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(lean_object* v_mutVarIdents_688_, lean_object* v_baseMonadInfo_689_, lean_object* v_00_u03c3_690_, lean_object* v_base_691_, lean_object* v_e_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(v_mutVarIdents_688_, v_baseMonadInfo_689_, v_00_u03c3_690_, v_base_691_, v_e_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5(lean_object* v_baseMonadInfo_705_, lean_object* v_mutVarIdents_706_, lean_object* v_base_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc_ref(v_baseMonadInfo_705_);
v___x_716_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(v_baseMonadInfo_705_, v_mutVarIdents_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_m_718_; lean_object* v___x_719_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v___x_716_);
v_m_718_ = lean_ctor_get(v_base_707_, 1);
lean_inc_ref(v_m_718_);
lean_dec_ref(v_base_707_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc_ref(v___y_708_);
v___x_719_ = lean_apply_8(v_m_718_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_735_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_735_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_735_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_735_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_u_724_; lean_object* v_v_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_u_724_ = lean_ctor_get(v_baseMonadInfo_705_, 1);
lean_inc(v_u_724_);
v_v_725_ = lean_ctor_get(v_baseMonadInfo_705_, 2);
lean_inc(v_v_725_);
lean_dec_ref(v_baseMonadInfo_705_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1));
v___x_727_ = lean_box(0);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v_v_725_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v_u_724_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_mkConst(v___x_726_, v___x_729_);
v___x_731_ = l_Lean_mkAppB(v___x_730_, v_a_717_, v_a_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_731_);
v___x_733_ = v___x_722_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_dec(v_a_717_);
lean_dec_ref(v_baseMonadInfo_705_);
return v___x_719_;
}
}
else
{
lean_dec_ref(v_base_707_);
lean_dec_ref(v_baseMonadInfo_705_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(lean_object* v_baseMonadInfo_736_, lean_object* v_mutVarIdents_737_, lean_object* v_base_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(v_baseMonadInfo_736_, v_mutVarIdents_737_, v_base_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_stateT(lean_object* v_baseMonadInfo_748_, lean_object* v_mutVarIdents_749_, lean_object* v_00_u03c3_750_, lean_object* v_base_751_){
_start:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_757_; 
lean_inc_ref(v_00_u03c3_750_);
lean_inc_ref_n(v_base_751_, 4);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__0), 3, 2);
lean_closure_set(v___f_752_, 0, v_base_751_);
lean_closure_set(v___f_752_, 1, v_00_u03c3_750_);
lean_inc_ref_n(v_mutVarIdents_749_, 3);
lean_inc_ref_n(v_baseMonadInfo_748_, 3);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed), 12, 3);
lean_closure_set(v___f_753_, 0, v_baseMonadInfo_748_);
lean_closure_set(v___f_753_, 1, v_mutVarIdents_749_);
lean_closure_set(v___f_753_, 2, v_base_751_);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed), 12, 3);
lean_closure_set(v___f_754_, 0, v_baseMonadInfo_748_);
lean_closure_set(v___f_754_, 1, v_mutVarIdents_749_);
lean_closure_set(v___f_754_, 2, v_base_751_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed), 13, 4);
lean_closure_set(v___f_755_, 0, v_mutVarIdents_749_);
lean_closure_set(v___f_755_, 1, v_baseMonadInfo_748_);
lean_closure_set(v___f_755_, 2, v_00_u03c3_750_);
lean_closure_set(v___f_755_, 3, v_base_751_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed), 11, 3);
lean_closure_set(v___f_756_, 0, v_baseMonadInfo_748_);
lean_closure_set(v___f_756_, 1, v_mutVarIdents_749_);
lean_closure_set(v___f_756_, 2, v_base_751_);
v___x_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_757_, 0, v___f_752_);
lean_ctor_set(v___x_757_, 1, v___f_756_);
lean_ctor_set(v___x_757_, 2, v___f_753_);
lean_ctor_set(v___x_757_, 3, v___f_755_);
lean_ctor_set(v___x_757_, 4, v___f_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(size_t v_sz_758_, size_t v_i_759_, lean_object* v_bs_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_758_, v_i_759_, v_bs_760_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(lean_object* v_sz_770_, lean_object* v_i_771_, lean_object* v_bs_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
size_t v_sz_boxed_781_; size_t v_i_boxed_782_; lean_object* v_res_783_; 
v_sz_boxed_781_ = lean_unbox_usize(v_sz_770_);
lean_dec(v_sz_770_);
v_i_boxed_782_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_781_, v_i_boxed_782_, v_bs_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(lean_object* v_baseMonadInfo_787_, lean_object* v_00_u03b1_788_){
_start:
{
lean_object* v_u_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_u_789_ = lean_ctor_get(v_baseMonadInfo_787_, 1);
v___x_790_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_791_ = lean_box(0);
lean_inc(v_u_789_);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v_u_789_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_mkConst(v___x_790_, v___x_792_);
v___x_794_ = l_Lean_Expr_app___override(v___x_793_, v_00_u03b1_788_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(lean_object* v_baseMonadInfo_795_, lean_object* v_00_u03b1_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_795_, v_00_u03b1_796_);
lean_dec_ref(v_baseMonadInfo_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0(lean_object* v_runInBase_803_, lean_object* v_e_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_813_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2));
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_mk_empty_array_with_capacity(v___x_814_);
v___x_816_ = lean_array_push(v___x_815_, v_e_804_);
v___x_817_ = l_Lean_Meta_mkAppM(v___x_813_, v___x_816_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_817_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc_ref(v___y_805_);
v___x_819_ = lean_apply_9(v_runInBase_803_, v_a_818_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, lean_box(0));
return v___x_819_;
}
else
{
lean_dec_ref(v_runInBase_803_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(lean_object* v_runInBase_820_, lean_object* v_e_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(v_runInBase_820_, v_e_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_830_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__1(lean_object* v_description_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_836_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1, &l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1);
v___x_837_ = lean_box(0);
v___x_838_ = lean_apply_1(v_description_834_, v___x_837_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_836_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2(lean_object* v_k_840_, lean_object* v_r_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc_ref(v___y_842_);
v___x_850_ = lean_apply_8(v_k_840_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, lean_box(0));
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; uint8_t v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = lean_mk_empty_array_with_capacity(v___x_852_);
v___x_854_ = lean_array_push(v___x_853_, v_r_841_);
v___x_855_ = 0;
v___x_856_ = 1;
v___x_857_ = 1;
v___x_858_ = l_Lean_Meta_mkLambdaFVars(v___x_854_, v_a_851_, v___x_855_, v___x_856_, v___x_855_, v___x_856_, v___x_857_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec_ref(v___x_854_);
return v___x_858_;
}
else
{
lean_dec_ref(v_r_841_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(lean_object* v_k_859_, lean_object* v_r_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(v_k_859_, v_r_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3(lean_object* v_a_870_, lean_object* v_r_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; 
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc_ref(v___y_872_);
v___x_880_ = lean_apply_8(v_a_870_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, lean_box(0));
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; uint8_t v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref(v___x_880_);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
v___x_884_ = lean_array_push(v___x_883_, v_r_871_);
v___x_885_ = 0;
v___x_886_ = 1;
v___x_887_ = 1;
v___x_888_ = l_Lean_Meta_mkLambdaFVars(v___x_884_, v_a_881_, v___x_885_, v___x_886_, v___x_885_, v___x_886_, v___x_887_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v___x_884_);
return v___x_888_;
}
else
{
lean_dec_ref(v_r_871_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(lean_object* v_a_889_, lean_object* v_r_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(v_a_889_, v_r_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(lean_object* v_k_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc_ref(v___y_901_);
v___x_910_ = lean_apply_9(v_k_900_, v_b_904_, v___y_901_, v___y_902_, v___y_903_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_911_, v___y_912_, v___y_913_, v___y_914_, v_b_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(lean_object* v_name_922_, uint8_t v_bi_923_, lean_object* v_type_924_, lean_object* v_k_925_, uint8_t v_kind_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___f_935_; lean_object* v___x_936_; 
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc_ref(v___y_927_);
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_935_, 0, v_k_925_);
lean_closure_set(v___f_935_, 1, v___y_927_);
lean_closure_set(v___f_935_, 2, v___y_928_);
lean_closure_set(v___f_935_, 3, v___y_929_);
v___x_936_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_922_, v_bi_923_, v_type_924_, v___f_935_, v_kind_926_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_936_) == 0)
{
return v___x_936_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(lean_object* v_name_945_, lean_object* v_bi_946_, lean_object* v_type_947_, lean_object* v_k_948_, lean_object* v_kind_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v_bi_boxed_958_; uint8_t v_kind_boxed_959_; lean_object* v_res_960_; 
v_bi_boxed_958_ = lean_unbox(v_bi_946_);
v_kind_boxed_959_ = lean_unbox(v_kind_949_);
v_res_960_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_945_, v_bi_boxed_958_, v_type_947_, v_k_948_, v_kind_boxed_959_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(lean_object* v_name_961_, lean_object* v_type_962_, lean_object* v_k_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v___x_972_ = 0;
v___x_973_ = 0;
v___x_974_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_961_, v___x_972_, v_type_962_, v_k_963_, v___x_973_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(lean_object* v_name_975_, lean_object* v_type_976_, lean_object* v_k_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_975_, v_type_976_, v_k_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_box(0);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3));
v___x_995_ = l_Lean_mkConst(v___x_994_, v___x_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4(lean_object* v_a_996_, lean_object* v_getCont_997_, lean_object* v_resultName_998_, lean_object* v_resultType_999_, lean_object* v___f_1000_, lean_object* v_baseMonadInfo_1001_, lean_object* v_casesOnWrapper_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_getFVarFromUserName(v_a_996_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1013_ = lean_apply_8(v_getCont_997_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, lean_box(0));
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1016_ = l_Lean_Core_mkFreshUserName(v___x_1015_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1018_, 0, v_a_1014_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4, &l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once, _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4);
v___x_1021_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1017_, v___x_1020_, v___f_1018_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
lean_inc_ref(v_resultType_999_);
v___x_1023_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_998_, v_resultType_999_, v___f_1000_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v_doBlockResultType_1025_; lean_object* v___x_1026_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v_doBlockResultType_1025_ = lean_ctor_get(v___y_1003_, 3);
lean_inc_ref(v_doBlockResultType_1025_);
v___x_1026_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_1025_, v___y_1003_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1040_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1040_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1040_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_u_1031_; lean_object* v_v_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v_u_1031_ = lean_ctor_get(v_baseMonadInfo_1001_, 1);
v_v_1032_ = lean_ctor_get(v_baseMonadInfo_1001_, 2);
lean_inc(v_v_1032_);
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_v_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_1019_);
lean_inc(v_u_1031_);
v___x_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_u_1031_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_mkConst(v_casesOnWrapper_1002_, v___x_1034_);
v___x_1036_ = l_Lean_mkApp5(v___x_1035_, v_resultType_999_, v_a_1027_, v_a_1012_, v_a_1022_, v_a_1024_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1036_);
v___x_1038_ = v___x_1029_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_dec(v_a_1024_);
lean_dec(v_a_1022_);
lean_dec(v_a_1012_);
lean_dec(v_casesOnWrapper_1002_);
lean_dec_ref(v_resultType_999_);
return v___x_1026_;
}
}
else
{
lean_dec(v_a_1022_);
lean_dec(v_a_1012_);
lean_dec(v_casesOnWrapper_1002_);
lean_dec_ref(v_resultType_999_);
return v___x_1023_;
}
}
else
{
lean_dec(v_a_1012_);
lean_dec(v_casesOnWrapper_1002_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v_resultType_999_);
lean_dec(v_resultName_998_);
return v___x_1021_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1014_);
lean_dec(v_a_1012_);
lean_dec(v_casesOnWrapper_1002_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v_resultType_999_);
lean_dec(v_resultName_998_);
v_a_1041_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1016_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1016_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1012_);
lean_dec(v_casesOnWrapper_1002_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v_resultType_999_);
lean_dec(v_resultName_998_);
v_a_1049_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1013_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1013_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_dec(v_casesOnWrapper_1002_);
lean_dec_ref(v___f_1000_);
lean_dec_ref(v_resultType_999_);
lean_dec(v_resultName_998_);
lean_dec_ref(v_getCont_997_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(lean_object* v_a_1057_, lean_object* v_getCont_1058_, lean_object* v_resultName_1059_, lean_object* v_resultType_1060_, lean_object* v___f_1061_, lean_object* v_baseMonadInfo_1062_, lean_object* v_casesOnWrapper_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(v_a_1057_, v_getCont_1058_, v_resultName_1059_, v_resultType_1060_, v___f_1061_, v_baseMonadInfo_1062_, v_casesOnWrapper_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec_ref(v_baseMonadInfo_1062_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5(lean_object* v_getCont_1076_, lean_object* v_baseMonadInfo_1077_, lean_object* v_casesOnWrapper_1078_, lean_object* v_restoreCont_1079_, lean_object* v_dec_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1090_ = l_Lean_Core_mkFreshUserName(v___x_1089_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v_resultName_1092_; lean_object* v_resultType_1093_; lean_object* v_k_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1106_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1090_);
v_resultName_1092_ = lean_ctor_get(v_dec_1080_, 0);
v_resultType_1093_ = lean_ctor_get(v_dec_1080_, 1);
v_k_1094_ = lean_ctor_get(v_dec_1080_, 2);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_dec_1080_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1096_ = v_dec_1080_;
v_isShared_1097_ = v_isSharedCheck_1106_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_k_1094_);
lean_inc(v_resultType_1093_);
lean_inc(v_resultName_1092_);
lean_dec(v_dec_1080_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1106_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___f_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1103_; 
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1098_, 0, v_k_1094_);
lean_inc_ref(v_baseMonadInfo_1077_);
lean_inc_ref(v_resultType_1093_);
lean_inc(v_a_1091_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed), 15, 7);
lean_closure_set(v___f_1099_, 0, v_a_1091_);
lean_closure_set(v___f_1099_, 1, v_getCont_1076_);
lean_closure_set(v___f_1099_, 2, v_resultName_1092_);
lean_closure_set(v___f_1099_, 3, v_resultType_1093_);
lean_closure_set(v___f_1099_, 4, v___f_1098_);
lean_closure_set(v___f_1099_, 5, v_baseMonadInfo_1077_);
lean_closure_set(v___f_1099_, 6, v_casesOnWrapper_1078_);
v___x_1100_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1077_, v_resultType_1093_);
lean_dec_ref(v_baseMonadInfo_1077_);
v___x_1101_ = 0;
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 2, v___f_1099_);
lean_ctor_set(v___x_1096_, 1, v___x_1100_);
lean_ctor_set(v___x_1096_, 0, v_a_1091_);
v___x_1103_ = v___x_1096_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1091_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v___f_1099_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*3, v___x_1101_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc_ref(v___y_1081_);
v___x_1104_ = lean_apply_9(v_restoreCont_1079_, v___x_1103_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, lean_box(0));
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_dec_1080_);
lean_dec_ref(v_restoreCont_1079_);
lean_dec(v_casesOnWrapper_1078_);
lean_dec_ref(v_baseMonadInfo_1077_);
lean_dec_ref(v_getCont_1076_);
v_a_1107_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1090_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1090_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(lean_object* v_getCont_1115_, lean_object* v_baseMonadInfo_1116_, lean_object* v_casesOnWrapper_1117_, lean_object* v_restoreCont_1118_, lean_object* v_dec_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(v_getCont_1115_, v_baseMonadInfo_1116_, v_casesOnWrapper_1117_, v_restoreCont_1118_, v_dec_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6(lean_object* v_baseMonadInfo_1129_, lean_object* v_stM_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(v_baseMonadInfo_1129_, v___y_1131_);
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
lean_inc_ref(v___y_1132_);
v___x_1141_ = lean_apply_9(v_stM_1130_, v___x_1140_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(lean_object* v_baseMonadInfo_1142_, lean_object* v_stM_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(v_baseMonadInfo_1142_, v_stM_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_baseMonadInfo_1142_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7(lean_object* v_m_1154_, lean_object* v_baseMonadInfo_1155_, lean_object* v_optionTWrapper_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc_ref(v___y_1157_);
v___x_1165_ = lean_apply_8(v_m_1154_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, lean_box(0));
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1180_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1180_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1180_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_u_1170_; lean_object* v_v_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v_u_1170_ = lean_ctor_get(v_baseMonadInfo_1155_, 1);
v_v_1171_ = lean_ctor_get(v_baseMonadInfo_1155_, 2);
v___x_1172_ = lean_box(0);
lean_inc(v_v_1171_);
v___x_1173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_v_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_inc(v_u_1170_);
v___x_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_u_1170_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_mkConst(v_optionTWrapper_1156_, v___x_1174_);
v___x_1176_ = l_Lean_Expr_app___override(v___x_1175_, v_a_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1176_);
v___x_1178_ = v___x_1168_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_dec(v_optionTWrapper_1156_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(lean_object* v_m_1181_, lean_object* v_baseMonadInfo_1182_, lean_object* v_optionTWrapper_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(v_m_1181_, v_baseMonadInfo_1182_, v_optionTWrapper_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec_ref(v_baseMonadInfo_1182_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_optionT(lean_object* v_baseMonadInfo_1193_, lean_object* v_optionTWrapper_1194_, lean_object* v_casesOnWrapper_1195_, lean_object* v_getCont_1196_, lean_object* v_base_1197_){
_start:
{
lean_object* v_description_1198_; lean_object* v_m_1199_; lean_object* v_stM_1200_; lean_object* v_runInBase_1201_; lean_object* v_restoreCont_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1214_; 
v_description_1198_ = lean_ctor_get(v_base_1197_, 0);
v_m_1199_ = lean_ctor_get(v_base_1197_, 1);
v_stM_1200_ = lean_ctor_get(v_base_1197_, 2);
v_runInBase_1201_ = lean_ctor_get(v_base_1197_, 3);
v_restoreCont_1202_ = lean_ctor_get(v_base_1197_, 4);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_base_1197_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1204_ = v_base_1197_;
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_restoreCont_1202_);
lean_inc(v_runInBase_1201_);
lean_inc(v_stM_1200_);
lean_inc(v_m_1199_);
lean_inc(v_description_1198_);
lean_dec(v_base_1197_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___x_1212_; 
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1206_, 0, v_runInBase_1201_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__1), 2, 1);
lean_closure_set(v___f_1207_, 0, v_description_1198_);
lean_inc_ref_n(v_baseMonadInfo_1193_, 2);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed), 13, 4);
lean_closure_set(v___f_1208_, 0, v_getCont_1196_);
lean_closure_set(v___f_1208_, 1, v_baseMonadInfo_1193_);
lean_closure_set(v___f_1208_, 2, v_casesOnWrapper_1195_);
lean_closure_set(v___f_1208_, 3, v_restoreCont_1202_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed), 11, 2);
lean_closure_set(v___f_1209_, 0, v_baseMonadInfo_1193_);
lean_closure_set(v___f_1209_, 1, v_stM_1200_);
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed), 11, 3);
lean_closure_set(v___f_1210_, 0, v_m_1199_);
lean_closure_set(v___f_1210_, 1, v_baseMonadInfo_1193_);
lean_closure_set(v___f_1210_, 2, v_optionTWrapper_1194_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 4, v___f_1208_);
lean_ctor_set(v___x_1204_, 3, v___f_1206_);
lean_ctor_set(v___x_1204_, 2, v___f_1209_);
lean_ctor_set(v___x_1204_, 1, v___f_1210_);
lean_ctor_set(v___x_1204_, 0, v___f_1207_);
v___x_1212_ = v___x_1204_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___f_1210_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v___f_1209_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v___f_1206_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v___f_1208_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(lean_object* v_00_u03b1_1215_, lean_object* v_name_1216_, uint8_t v_bi_1217_, lean_object* v_type_1218_, lean_object* v_k_1219_, uint8_t v_kind_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_1216_, v_bi_1217_, v_type_1218_, v_k_1219_, v_kind_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_name_1231_, lean_object* v_bi_1232_, lean_object* v_type_1233_, lean_object* v_k_1234_, lean_object* v_kind_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_bi_boxed_1244_; uint8_t v_kind_boxed_1245_; lean_object* v_res_1246_; 
v_bi_boxed_1244_ = lean_unbox(v_bi_1232_);
v_kind_boxed_1245_ = lean_unbox(v_kind_1235_);
v_res_1246_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_1230_, v_name_1231_, v_bi_boxed_1244_, v_type_1233_, v_k_1234_, v_kind_boxed_1245_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(lean_object* v_00_u03b1_1247_, lean_object* v_name_1248_, lean_object* v_type_1249_, lean_object* v_k_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_name_1248_, v_type_1249_, v_k_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_name_1261_, lean_object* v_type_1262_, lean_object* v_k_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(v_00_u03b1_1260_, v_name_1261_, v_type_1262_, v_k_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(lean_object* v_baseMonadInfo_1276_, lean_object* v_getCont_1277_, lean_object* v_00_u03b1_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; 
lean_inc(v_a_1285_);
lean_inc_ref(v_a_1284_);
lean_inc(v_a_1283_);
lean_inc_ref(v_a_1282_);
lean_inc(v_a_1281_);
lean_inc_ref(v_a_1280_);
lean_inc_ref(v_a_1279_);
v___x_1287_ = lean_apply_8(v_getCont_1277_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, lean_box(0));
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1310_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1310_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1310_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_u_1292_; lean_object* v_resultType_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1308_; 
v_u_1292_ = lean_ctor_get(v_baseMonadInfo_1276_, 1);
v_resultType_1293_ = lean_ctor_get(v_a_1288_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v_a_1288_, 1);
lean_dec(v_unused_1309_);
v___x_1295_ = v_a_1288_;
v_isShared_1296_ = v_isSharedCheck_1308_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_resultType_1293_);
lean_dec(v_a_1288_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1308_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(0);
lean_inc(v_u_1292_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 1);
lean_ctor_set(v___x_1295_, 1, v___x_1297_);
lean_ctor_set(v___x_1295_, 0, v_u_1292_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_u_1292_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1300_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
lean_inc(v_u_1292_);
v___x_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_u_1292_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
v___x_1302_ = l_Lean_mkConst(v___x_1300_, v___x_1301_);
v___x_1303_ = l_Lean_mkAppB(v___x_1302_, v_resultType_1293_, v_00_u03b1_1278_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1303_);
v___x_1305_ = v___x_1290_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_00_u03b1_1278_);
v_a_1311_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1287_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1287_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(lean_object* v_baseMonadInfo_1319_, lean_object* v_getCont_1320_, lean_object* v_00_u03b1_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1319_, v_getCont_1320_, v_00_u03b1_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec_ref(v_baseMonadInfo_1319_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0(lean_object* v_k_1331_, lean_object* v_r_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc_ref(v___y_1333_);
v___x_1341_ = lean_apply_8(v_k_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; uint8_t v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_n(v_a_1342_, 2);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_mk_empty_array_with_capacity(v___x_1343_);
v___x_1345_ = lean_array_push(v___x_1344_, v_r_1332_);
v___x_1346_ = 0;
v___x_1347_ = 1;
v___x_1348_ = 1;
v___x_1349_ = l_Lean_Meta_mkLambdaFVars(v___x_1345_, v_a_1342_, v___x_1346_, v___x_1347_, v___x_1346_, v___x_1347_, v___x_1348_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v___x_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v___x_1349_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
v___x_1351_ = lean_infer_type(v_a_1342_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_a_1350_);
lean_ctor_set(v___x_1356_, 1, v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1350_);
v_a_1361_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1351_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1351_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_a_1342_);
v_a_1369_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1349_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1349_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_r_1332_);
v_a_1377_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1341_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1341_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(lean_object* v_k_1385_, lean_object* v_r_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(v_k_1385_, v_r_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1(lean_object* v_k_1396_, lean_object* v_r_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc_ref(v_r_1397_);
v___x_1406_ = lean_apply_9(v_k_1396_, v_r_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, lean_box(0));
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; uint8_t v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1408_);
v___x_1410_ = lean_array_push(v___x_1409_, v_r_1397_);
v___x_1411_ = 0;
v___x_1412_ = 1;
v___x_1413_ = 1;
v___x_1414_ = l_Lean_Meta_mkLambdaFVars(v___x_1410_, v_a_1407_, v___x_1411_, v___x_1412_, v___x_1411_, v___x_1412_, v___x_1413_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec_ref(v___x_1410_);
return v___x_1414_;
}
else
{
lean_dec_ref(v_r_1397_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(lean_object* v_k_1415_, lean_object* v_r_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(v_k_1415_, v_r_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2(lean_object* v_a_1426_, lean_object* v_getCont_1427_, lean_object* v_resultName_1428_, lean_object* v_resultType_1429_, lean_object* v___f_1430_, lean_object* v_baseMonadInfo_1431_, lean_object* v_casesOnWrapper_1432_, lean_object* v_00_u03b5_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Meta_getFVarFromUserName(v_a_1426_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref(v___x_1442_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc_ref(v___y_1434_);
v___x_1444_ = lean_apply_8(v_getCont_1427_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, lean_box(0));
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1));
v___x_1447_ = l_Lean_Core_mkFreshUserName(v___x_1446_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v_resultType_1449_; lean_object* v_k_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1491_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v___x_1447_);
v_resultType_1449_ = lean_ctor_get(v_a_1445_, 0);
v_k_1450_ = lean_ctor_get(v_a_1445_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_a_1445_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1452_ = v_a_1445_;
v_isShared_1453_ = v_isSharedCheck_1491_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_k_1450_);
lean_inc(v_resultType_1449_);
lean_dec(v_a_1445_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1491_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___f_1454_; lean_object* v___x_1455_; 
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1454_, 0, v_k_1450_);
v___x_1455_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_1448_, v_resultType_1449_, v___f_1454_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
lean_inc_ref(v_resultType_1429_);
v___x_1457_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_1428_, v_resultType_1429_, v___f_1430_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1482_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1482_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1482_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v_fst_1462_; lean_object* v_snd_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1481_; 
v_fst_1462_ = lean_ctor_get(v_a_1458_, 0);
v_snd_1463_ = lean_ctor_get(v_a_1458_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_a_1458_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1465_ = v_a_1458_;
v_isShared_1466_ = v_isSharedCheck_1481_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_snd_1463_);
lean_inc(v_fst_1462_);
lean_dec(v_a_1458_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1481_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_u_1467_; lean_object* v_v_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v_u_1467_ = lean_ctor_get(v_baseMonadInfo_1431_, 1);
v_v_1468_ = lean_ctor_get(v_baseMonadInfo_1431_, 2);
v___x_1469_ = lean_box(0);
lean_inc(v_v_1468_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set_tag(v___x_1465_, 1);
lean_ctor_set(v___x_1465_, 1, v___x_1469_);
lean_ctor_set(v___x_1465_, 0, v_v_1468_);
v___x_1471_ = v___x_1465_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_v_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
lean_inc(v_u_1467_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 1, v___x_1471_);
lean_ctor_set(v___x_1452_, 0, v_u_1467_);
v___x_1473_ = v___x_1452_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_u_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1474_ = l_Lean_mkConst(v_casesOnWrapper_1432_, v___x_1473_);
v___x_1475_ = l_Lean_mkApp6(v___x_1474_, v_00_u03b5_1433_, v_resultType_1429_, v_snd_1463_, v_a_1443_, v_a_1456_, v_fst_1462_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1475_);
v___x_1477_ = v___x_1460_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_a_1456_);
lean_del_object(v___x_1452_);
lean_dec(v_a_1443_);
lean_dec_ref(v_00_u03b5_1433_);
lean_dec(v_casesOnWrapper_1432_);
lean_dec_ref(v_resultType_1429_);
v_a_1483_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1457_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1457_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_del_object(v___x_1452_);
lean_dec(v_a_1443_);
lean_dec_ref(v_00_u03b5_1433_);
lean_dec(v_casesOnWrapper_1432_);
lean_dec_ref(v___f_1430_);
lean_dec_ref(v_resultType_1429_);
lean_dec(v_resultName_1428_);
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1445_);
lean_dec(v_a_1443_);
lean_dec_ref(v_00_u03b5_1433_);
lean_dec(v_casesOnWrapper_1432_);
lean_dec_ref(v___f_1430_);
lean_dec_ref(v_resultType_1429_);
lean_dec(v_resultName_1428_);
v_a_1492_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1447_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1447_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1443_);
lean_dec_ref(v_00_u03b5_1433_);
lean_dec(v_casesOnWrapper_1432_);
lean_dec_ref(v___f_1430_);
lean_dec_ref(v_resultType_1429_);
lean_dec(v_resultName_1428_);
v_a_1500_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1444_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1444_);
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
lean_dec_ref(v_00_u03b5_1433_);
lean_dec(v_casesOnWrapper_1432_);
lean_dec_ref(v___f_1430_);
lean_dec_ref(v_resultType_1429_);
lean_dec(v_resultName_1428_);
lean_dec_ref(v_getCont_1427_);
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(lean_object* v_a_1508_, lean_object* v_getCont_1509_, lean_object* v_resultName_1510_, lean_object* v_resultType_1511_, lean_object* v___f_1512_, lean_object* v_baseMonadInfo_1513_, lean_object* v_casesOnWrapper_1514_, lean_object* v_00_u03b5_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(v_a_1508_, v_getCont_1509_, v_resultName_1510_, v_resultType_1511_, v___f_1512_, v_baseMonadInfo_1513_, v_casesOnWrapper_1514_, v_00_u03b5_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_baseMonadInfo_1513_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3(lean_object* v_baseMonadInfo_1525_, lean_object* v_getCont_1526_, lean_object* v_casesOnWrapper_1527_, lean_object* v_00_u03b5_1528_, lean_object* v_restoreCont_1529_, lean_object* v_dec_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1));
v___x_1540_ = l_Lean_Core_mkFreshUserName(v___x_1539_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v_resultName_1542_; lean_object* v_resultType_1543_; lean_object* v_k_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1565_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v_resultName_1542_ = lean_ctor_get(v_dec_1530_, 0);
v_resultType_1543_ = lean_ctor_get(v_dec_1530_, 1);
v_k_1544_ = lean_ctor_get(v_dec_1530_, 2);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_dec_1530_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1546_ = v_dec_1530_;
v_isShared_1547_ = v_isSharedCheck_1565_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_k_1544_);
lean_inc(v_resultType_1543_);
lean_inc(v_resultName_1542_);
lean_dec(v_dec_1530_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1565_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; 
lean_inc_ref(v_resultType_1543_);
lean_inc_ref(v_getCont_1526_);
v___x_1548_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1525_, v_getCont_1526_, v_resultType_1543_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___f_1550_; lean_object* v___f_1551_; uint8_t v___x_1552_; lean_object* v___x_1554_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1550_, 0, v_k_1544_);
lean_inc(v_a_1541_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed), 16, 8);
lean_closure_set(v___f_1551_, 0, v_a_1541_);
lean_closure_set(v___f_1551_, 1, v_getCont_1526_);
lean_closure_set(v___f_1551_, 2, v_resultName_1542_);
lean_closure_set(v___f_1551_, 3, v_resultType_1543_);
lean_closure_set(v___f_1551_, 4, v___f_1550_);
lean_closure_set(v___f_1551_, 5, v_baseMonadInfo_1525_);
lean_closure_set(v___f_1551_, 6, v_casesOnWrapper_1527_);
lean_closure_set(v___f_1551_, 7, v_00_u03b5_1528_);
v___x_1552_ = 0;
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 2, v___f_1551_);
lean_ctor_set(v___x_1546_, 1, v_a_1549_);
lean_ctor_set(v___x_1546_, 0, v_a_1541_);
v___x_1554_ = v___x_1546_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1541_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_a_1549_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v___f_1551_);
v___x_1554_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; 
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*3, v___x_1552_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
lean_inc_ref(v___y_1531_);
v___x_1555_ = lean_apply_9(v_restoreCont_1529_, v___x_1554_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, lean_box(0));
return v___x_1555_;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1546_);
lean_dec_ref(v_k_1544_);
lean_dec_ref(v_resultType_1543_);
lean_dec(v_resultName_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_restoreCont_1529_);
lean_dec_ref(v_00_u03b5_1528_);
lean_dec(v_casesOnWrapper_1527_);
lean_dec_ref(v_getCont_1526_);
lean_dec_ref(v_baseMonadInfo_1525_);
v_a_1557_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1548_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1548_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_dec_1530_);
lean_dec_ref(v_restoreCont_1529_);
lean_dec_ref(v_00_u03b5_1528_);
lean_dec(v_casesOnWrapper_1527_);
lean_dec_ref(v_getCont_1526_);
lean_dec_ref(v_baseMonadInfo_1525_);
v_a_1566_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1540_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1540_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(lean_object* v_baseMonadInfo_1574_, lean_object* v_getCont_1575_, lean_object* v_casesOnWrapper_1576_, lean_object* v_00_u03b5_1577_, lean_object* v_restoreCont_1578_, lean_object* v_dec_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(v_baseMonadInfo_1574_, v_getCont_1575_, v_casesOnWrapper_1576_, v_00_u03b5_1577_, v_restoreCont_1578_, v_dec_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1588_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2));
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__4(lean_object* v_00_u03b5_1595_, lean_object* v_description_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1598_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1);
v___x_1599_ = l_Lean_MessageData_ofExpr(v_00_u03b5_1595_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3, &l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once, _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3);
v___x_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_apply_1(v_description_1596_, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1602_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5(lean_object* v_baseMonadInfo_1606_, lean_object* v_getCont_1607_, lean_object* v_stM_1608_, lean_object* v_00_u03b1_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(v_baseMonadInfo_1606_, v_getCont_1607_, v_00_u03b1_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc_ref(v___y_1610_);
v___x_1620_ = lean_apply_9(v_stM_1608_, v_a_1619_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, lean_box(0));
return v___x_1620_;
}
else
{
lean_dec_ref(v_stM_1608_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(lean_object* v_baseMonadInfo_1621_, lean_object* v_getCont_1622_, lean_object* v_stM_1623_, lean_object* v_00_u03b1_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(v_baseMonadInfo_1621_, v_getCont_1622_, v_stM_1623_, v_00_u03b1_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v_baseMonadInfo_1621_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6(lean_object* v_runInBase_1638_, lean_object* v_e_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1));
v___x_1649_ = lean_unsigned_to_nat(1u);
v___x_1650_ = lean_mk_empty_array_with_capacity(v___x_1649_);
v___x_1651_ = lean_array_push(v___x_1650_, v_e_1639_);
v___x_1652_ = l_Lean_Meta_mkAppM(v___x_1648_, v___x_1651_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc_ref(v___y_1640_);
v___x_1654_ = lean_apply_9(v_runInBase_1638_, v_a_1653_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, lean_box(0));
return v___x_1654_;
}
else
{
lean_dec_ref(v_runInBase_1638_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(lean_object* v_runInBase_1655_, lean_object* v_e_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(v_runInBase_1655_, v_e_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7(lean_object* v_m_1666_, lean_object* v_baseMonadInfo_1667_, lean_object* v_exceptTWrapper_1668_, lean_object* v_00_u03b5_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v___y_1674_);
lean_inc_ref(v___y_1673_);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc_ref(v___y_1670_);
v___x_1678_ = lean_apply_8(v_m_1666_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, lean_box(0));
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1693_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1693_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1693_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_u_1683_; lean_object* v_v_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v_u_1683_ = lean_ctor_get(v_baseMonadInfo_1667_, 1);
v_v_1684_ = lean_ctor_get(v_baseMonadInfo_1667_, 2);
v___x_1685_ = lean_box(0);
lean_inc(v_v_1684_);
v___x_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_v_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
lean_inc(v_u_1683_);
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_u_1683_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_mkConst(v_exceptTWrapper_1668_, v___x_1687_);
v___x_1689_ = l_Lean_mkAppB(v___x_1688_, v_00_u03b5_1669_, v_a_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1689_);
v___x_1691_ = v___x_1681_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_dec_ref(v_00_u03b5_1669_);
lean_dec(v_exceptTWrapper_1668_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(lean_object* v_m_1694_, lean_object* v_baseMonadInfo_1695_, lean_object* v_exceptTWrapper_1696_, lean_object* v_00_u03b5_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(v_m_1694_, v_baseMonadInfo_1695_, v_exceptTWrapper_1696_, v_00_u03b5_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec_ref(v_baseMonadInfo_1695_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_exceptT(lean_object* v_baseMonadInfo_1707_, lean_object* v_exceptTWrapper_1708_, lean_object* v_casesOnWrapper_1709_, lean_object* v_getCont_1710_, lean_object* v_00_u03b5_1711_, lean_object* v_base_1712_){
_start:
{
lean_object* v_description_1713_; lean_object* v_m_1714_; lean_object* v_stM_1715_; lean_object* v_runInBase_1716_; lean_object* v_restoreCont_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1729_; 
v_description_1713_ = lean_ctor_get(v_base_1712_, 0);
v_m_1714_ = lean_ctor_get(v_base_1712_, 1);
v_stM_1715_ = lean_ctor_get(v_base_1712_, 2);
v_runInBase_1716_ = lean_ctor_get(v_base_1712_, 3);
v_restoreCont_1717_ = lean_ctor_get(v_base_1712_, 4);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_base_1712_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1719_ = v_base_1712_;
v_isShared_1720_ = v_isSharedCheck_1729_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_restoreCont_1717_);
lean_inc(v_runInBase_1716_);
lean_inc(v_stM_1715_);
lean_inc(v_m_1714_);
lean_inc(v_description_1713_);
lean_dec(v_base_1712_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1729_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___x_1727_; 
lean_inc_ref_n(v_00_u03b5_1711_, 2);
lean_inc_ref(v_getCont_1710_);
lean_inc_ref_n(v_baseMonadInfo_1707_, 2);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed), 14, 5);
lean_closure_set(v___f_1721_, 0, v_baseMonadInfo_1707_);
lean_closure_set(v___f_1721_, 1, v_getCont_1710_);
lean_closure_set(v___f_1721_, 2, v_casesOnWrapper_1709_);
lean_closure_set(v___f_1721_, 3, v_00_u03b5_1711_);
lean_closure_set(v___f_1721_, 4, v_restoreCont_1717_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__4), 3, 2);
lean_closure_set(v___f_1722_, 0, v_00_u03b5_1711_);
lean_closure_set(v___f_1722_, 1, v_description_1713_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed), 12, 3);
lean_closure_set(v___f_1723_, 0, v_baseMonadInfo_1707_);
lean_closure_set(v___f_1723_, 1, v_getCont_1710_);
lean_closure_set(v___f_1723_, 2, v_stM_1715_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed), 10, 1);
lean_closure_set(v___f_1724_, 0, v_runInBase_1716_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed), 12, 4);
lean_closure_set(v___f_1725_, 0, v_m_1714_);
lean_closure_set(v___f_1725_, 1, v_baseMonadInfo_1707_);
lean_closure_set(v___f_1725_, 2, v_exceptTWrapper_1708_);
lean_closure_set(v___f_1725_, 3, v_00_u03b5_1711_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v___f_1721_);
lean_ctor_set(v___x_1719_, 3, v___f_1724_);
lean_ctor_set(v___x_1719_, 2, v___f_1723_);
lean_ctor_set(v___x_1719_, 1, v___f_1725_);
lean_ctor_set(v___x_1719_, 0, v___f_1722_);
v___x_1727_ = v___x_1719_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___f_1722_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___f_1725_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v___f_1723_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v___f_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v___f_1721_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_earlyReturnT(lean_object* v_baseMonadInfo_1739_, lean_object* v_00_u03c1_1740_, lean_object* v_m_1741_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1));
v___x_1743_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4));
v___x_1744_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5));
v___x_1745_ = l_Lean_Elab_Do_ControlStack_exceptT(v_baseMonadInfo_1739_, v___x_1742_, v___x_1743_, v___x_1744_, v_00_u03c1_1740_, v_m_1741_);
return v___x_1745_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0));
v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0(lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_1749_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
if (lean_obj_tag(v_a_1758_) == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_del_object(v___x_1760_);
v___x_1762_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1);
v___x_1763_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1762_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1763_;
}
else
{
lean_object* v_val_1764_; lean_object* v___x_1766_; 
v_val_1764_ = lean_ctor_get(v_a_1758_, 0);
lean_inc(v_val_1764_);
lean_dec_ref(v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v_val_1764_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_val_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1757_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1757_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v___y_1777_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_breakT(lean_object* v_baseMonadInfo_1794_, lean_object* v_m_1795_){
_start:
{
lean_object* v_getCont_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_getCont_1796_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__0));
v___x_1797_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__2));
v___x_1798_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_breakT___closed__4));
v___x_1799_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1794_, v___x_1797_, v___x_1798_, v_getCont_1796_, v_m_1795_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0(lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_1803_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1822_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1822_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1822_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
if (lean_obj_tag(v_a_1812_) == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_del_object(v___x_1814_);
v___x_1816_ = lean_obj_once(&l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1, &l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once, _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1);
v___x_1817_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1816_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1817_;
}
else
{
lean_object* v_val_1818_; lean_object* v___x_1820_; 
v_val_1818_ = lean_ctor_get(v_a_1812_, 0);
lean_inc(v_val_1818_);
lean_dec_ref(v_a_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_val_1818_);
v___x_1820_ = v___x_1814_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_val_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1811_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1811_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_continueT(lean_object* v_baseMonadInfo_1848_, lean_object* v_m_1849_){
_start:
{
lean_object* v_getCont_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_getCont_1850_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__0));
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__2));
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_continueT___closed__4));
v___x_1853_ = l_Lean_Elab_Do_ControlStack_optionT(v_baseMonadInfo_1848_, v___x_1851_, v___x_1852_, v_getCont_1850_, v_m_1849_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(lean_object* v_mi_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_m_1865_; lean_object* v_u_1866_; lean_object* v_v_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_m_1865_ = lean_ctor_get(v_mi_1857_, 0);
lean_inc_ref(v_m_1865_);
v_u_1866_ = lean_ctor_get(v_mi_1857_, 1);
lean_inc(v_u_1866_);
v_v_1867_ = lean_ctor_get(v_mi_1857_, 2);
lean_inc(v_v_1867_);
lean_dec_ref(v_mi_1857_);
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1));
v___x_1869_ = lean_box(0);
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_v_1867_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_u_1866_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_mkConst(v___x_1868_, v___x_1871_);
v___x_1873_ = l_Lean_Expr_app___override(v___x_1872_, v_m_1865_);
v___x_1874_ = lean_box(0);
v___x_1875_ = l_Lean_Elab_Term_mkInstMVar(v___x_1873_, v___x_1874_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(lean_object* v_mi_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v_mi_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
return v_res_1884_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2));
v___x_1890_ = l_Lean_stringToMessageData(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4));
v___x_1893_ = l_Lean_stringToMessageData(v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6));
v___x_1896_ = l_Lean_stringToMessageData(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(lean_object* v_msg_1897_, lean_object* v_expected_1898_, lean_object* v_actual_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; 
lean_inc_ref(v_actual_1899_);
lean_inc_ref(v_expected_1898_);
v___x_1905_ = l_Lean_Meta_isExprDefEq(v_expected_1898_, v_actual_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1929_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1929_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1929_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_unbox(v_a_1906_);
lean_dec(v_a_1906_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_del_object(v___x_1908_);
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
v___x_1912_ = l_Lean_stringToMessageData(v_msg_1897_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_MessageData_ofExpr(v_expected_1898_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_MessageData_ofExpr(v_actual_1899_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7, &l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once, _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(v___x_1923_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_dec_ref(v_actual_1899_);
lean_dec_ref(v_expected_1898_);
lean_dec_ref(v_msg_1897_);
v___x_1925_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1925_);
v___x_1927_ = v___x_1908_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_actual_1899_);
lean_dec_ref(v_expected_1898_);
lean_dec_ref(v_msg_1897_);
v_a_1930_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1905_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1905_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(lean_object* v_msg_1938_, lean_object* v_expected_1939_, lean_object* v_actual_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1938_, v_expected_1939_, v_actual_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(lean_object* v_msg_1947_, lean_object* v_expected_1948_, lean_object* v_actual_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v_msg_1947_, v_expected_1948_, v_actual_1949_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(lean_object* v_msg_1959_, lean_object* v_expected_1960_, lean_object* v_actual_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(v_msg_1959_, v_expected_1960_, v_actual_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec_ref(v_a_1962_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak(lean_object* v_base_1976_, uint8_t v_hasContinue_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_m_1986_; lean_object* v_runInBase_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2045_; 
v_m_1986_ = lean_ctor_get(v_base_1976_, 1);
v_runInBase_1987_ = lean_ctor_get(v_base_1976_, 3);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_base_1976_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2046_ = lean_ctor_get(v_base_1976_, 4);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_base_1976_, 2);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_base_1976_, 0);
lean_dec(v_unused_2048_);
v___x_1989_ = v_base_1976_;
v_isShared_1990_ = v_isSharedCheck_2045_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_runInBase_1987_);
lean_inc(v_m_1986_);
lean_dec(v_base_1976_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2045_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; 
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc_ref(v_a_1978_);
v___x_1991_ = lean_apply_8(v_m_1986_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, lean_box(0));
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_monadInfo_1992_; lean_object* v_a_1993_; lean_object* v_doBlockResultType_1994_; lean_object* v_u_1995_; lean_object* v_v_1996_; lean_object* v_cachedPUnit_1997_; lean_object* v_cachedPUnitUnit_1998_; lean_object* v___x_2000_; 
v_monadInfo_1992_ = lean_ctor_get(v_a_1978_, 0);
v_a_1993_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_n(v_a_1993_, 2);
lean_dec_ref(v___x_1991_);
v_doBlockResultType_1994_ = lean_ctor_get(v_a_1978_, 3);
v_u_1995_ = lean_ctor_get(v_monadInfo_1992_, 1);
v_v_1996_ = lean_ctor_get(v_monadInfo_1992_, 2);
v_cachedPUnit_1997_ = lean_ctor_get(v_monadInfo_1992_, 3);
v_cachedPUnitUnit_1998_ = lean_ctor_get(v_monadInfo_1992_, 4);
lean_inc_ref(v_cachedPUnitUnit_1998_);
lean_inc_ref(v_cachedPUnit_1997_);
lean_inc(v_v_1996_);
lean_inc(v_u_1995_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v_cachedPUnitUnit_1998_);
lean_ctor_set(v___x_1989_, 3, v_cachedPUnit_1997_);
lean_ctor_set(v___x_1989_, 2, v_v_1996_);
lean_ctor_set(v___x_1989_, 1, v_u_1995_);
lean_ctor_set(v___x_1989_, 0, v_a_1993_);
v___x_2000_ = v___x_1989_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_1993_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_u_1995_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_cachedPUnit_1997_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_cachedPUnitUnit_1998_);
v___x_2000_ = v_reuseFailAlloc_2044_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; 
v___x_2001_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2000_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_2001_);
v___x_2003_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2004_ = 0;
v___x_2005_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2003_, v___x_2004_, v_a_1978_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___y_2008_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
if (v_hasContinue_1977_ == 0)
{
v___y_2008_ = v_a_2006_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2039_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1));
v___x_2040_ = lean_box(0);
lean_inc(v_u_1995_);
v___x_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2041_, 0, v_u_1995_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_mkConst(v___x_2039_, v___x_2041_);
v___x_2043_ = l_Lean_Expr_app___override(v___x_2042_, v_a_2006_);
v___y_2008_ = v___x_2043_;
goto v___jp_2007_;
}
v___jp_2007_:
{
lean_object* v___x_2009_; 
lean_inc_ref(v_doBlockResultType_1994_);
v___x_2009_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_1994_, v_a_1978_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1));
v___x_2012_ = lean_box(0);
lean_inc(v_v_1996_);
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_v_1996_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
lean_inc(v_u_1995_);
v___x_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_u_1995_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_mkConst(v___x_2011_, v___x_2014_);
v___x_2016_ = l_Lean_mkApp3(v___x_2015_, v___y_2008_, v_a_1993_, v_a_2002_);
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc_ref(v_a_1978_);
v___x_2017_ = lean_apply_9(v_runInBase_1987_, v___x_2016_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, lean_box(0));
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_n(v_a_2018_, 2);
lean_dec_ref(v___x_2017_);
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
v___x_2019_ = lean_infer_type(v_a_2018_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref(v___x_2019_);
v___x_2021_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2));
v___x_2022_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2021_, v_a_2010_, v_a_2020_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2022_, 0);
lean_dec(v_unused_2030_);
v___x_2024_ = v___x_2022_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v___x_2022_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v_a_2018_);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2018_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_a_2018_);
v_a_2031_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2022_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2022_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_dec(v_a_2018_);
lean_dec(v_a_2010_);
return v___x_2019_;
}
}
else
{
lean_dec(v_a_2010_);
return v___x_2017_;
}
}
else
{
lean_dec_ref(v___y_2008_);
lean_dec(v_a_2002_);
lean_dec(v_a_1993_);
lean_dec_ref(v_runInBase_1987_);
return v___x_2009_;
}
}
}
else
{
lean_dec(v_a_2002_);
lean_dec(v_a_1993_);
lean_dec_ref(v_runInBase_1987_);
return v___x_2005_;
}
}
else
{
lean_dec(v_a_1993_);
lean_dec_ref(v_runInBase_1987_);
return v___x_2001_;
}
}
}
else
{
lean_del_object(v___x_1989_);
lean_dec_ref(v_runInBase_1987_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkBreak___boxed(lean_object* v_base_2049_, lean_object* v_hasContinue_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
uint8_t v_hasContinue_boxed_2059_; lean_object* v_res_2060_; 
v_hasContinue_boxed_2059_ = lean_unbox(v_hasContinue_2050_);
v_res_2060_ = l_Lean_Elab_Do_ControlStack_mkBreak(v_base_2049_, v_hasContinue_boxed_2059_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec_ref(v_a_2051_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue(lean_object* v_base_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_m_2075_; lean_object* v_runInBase_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2127_; 
v_m_2075_ = lean_ctor_get(v_base_2066_, 1);
v_runInBase_2076_ = lean_ctor_get(v_base_2066_, 3);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_base_2066_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; 
v_unused_2128_ = lean_ctor_get(v_base_2066_, 4);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_base_2066_, 2);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_base_2066_, 0);
lean_dec(v_unused_2130_);
v___x_2078_ = v_base_2066_;
v_isShared_2079_ = v_isSharedCheck_2127_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_runInBase_2076_);
lean_inc(v_m_2075_);
lean_dec(v_base_2066_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2127_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; 
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2070_);
lean_inc(v_a_2069_);
lean_inc_ref(v_a_2068_);
lean_inc_ref(v_a_2067_);
v___x_2080_ = lean_apply_8(v_m_2075_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, lean_box(0));
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_monadInfo_2081_; lean_object* v_a_2082_; lean_object* v_doBlockResultType_2083_; lean_object* v_u_2084_; lean_object* v_v_2085_; lean_object* v_cachedPUnit_2086_; lean_object* v_cachedPUnitUnit_2087_; lean_object* v___x_2089_; 
v_monadInfo_2081_ = lean_ctor_get(v_a_2067_, 0);
v_a_2082_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_n(v_a_2082_, 2);
lean_dec_ref(v___x_2080_);
v_doBlockResultType_2083_ = lean_ctor_get(v_a_2067_, 3);
v_u_2084_ = lean_ctor_get(v_monadInfo_2081_, 1);
v_v_2085_ = lean_ctor_get(v_monadInfo_2081_, 2);
v_cachedPUnit_2086_ = lean_ctor_get(v_monadInfo_2081_, 3);
v_cachedPUnitUnit_2087_ = lean_ctor_get(v_monadInfo_2081_, 4);
lean_inc_ref(v_cachedPUnitUnit_2087_);
lean_inc_ref(v_cachedPUnit_2086_);
lean_inc(v_v_2085_);
lean_inc(v_u_2084_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 4, v_cachedPUnitUnit_2087_);
lean_ctor_set(v___x_2078_, 3, v_cachedPUnit_2086_);
lean_ctor_set(v___x_2078_, 2, v_v_2085_);
lean_ctor_set(v___x_2078_, 1, v_u_2084_);
lean_ctor_set(v___x_2078_, 0, v_a_2082_);
v___x_2089_ = v___x_2078_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2082_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_u_2084_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_cachedPUnit_2086_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_cachedPUnitUnit_2087_);
v___x_2089_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2089_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_unStM___closed__1));
v___x_2093_ = 0;
v___x_2094_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2092_, v___x_2093_, v_a_2067_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
lean_inc_ref(v_doBlockResultType_2083_);
v___x_2096_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2083_, v_a_2067_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1));
v___x_2099_ = lean_box(0);
lean_inc(v_v_2085_);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_v_2085_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
lean_inc(v_u_2084_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_u_2084_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = l_Lean_mkConst(v___x_2098_, v___x_2101_);
v___x_2103_ = l_Lean_mkApp3(v___x_2102_, v_a_2095_, v_a_2082_, v_a_2091_);
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2070_);
lean_inc(v_a_2069_);
lean_inc_ref(v_a_2068_);
lean_inc_ref(v_a_2067_);
v___x_2104_ = lean_apply_9(v_runInBase_2076_, v___x_2103_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, lean_box(0));
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc_n(v_a_2105_, 2);
lean_dec_ref(v___x_2104_);
lean_inc(v_a_2073_);
lean_inc_ref(v_a_2072_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2070_);
v___x_2106_ = lean_infer_type(v_a_2105_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2));
v___x_2109_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2108_, v_a_2097_, v_a_2107_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2117_);
v___x_2111_ = v___x_2109_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2109_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v_a_2105_);
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2105_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_a_2105_);
v_a_2118_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2109_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2109_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_dec(v_a_2105_);
lean_dec(v_a_2097_);
return v___x_2106_;
}
}
else
{
lean_dec(v_a_2097_);
return v___x_2104_;
}
}
else
{
lean_dec(v_a_2095_);
lean_dec(v_a_2091_);
lean_dec(v_a_2082_);
lean_dec_ref(v_runInBase_2076_);
return v___x_2096_;
}
}
else
{
lean_dec(v_a_2091_);
lean_dec(v_a_2082_);
lean_dec_ref(v_runInBase_2076_);
return v___x_2094_;
}
}
else
{
lean_dec(v_a_2082_);
lean_dec_ref(v_runInBase_2076_);
return v___x_2090_;
}
}
}
else
{
lean_del_object(v___x_2078_);
lean_dec_ref(v_runInBase_2076_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkContinue___boxed(lean_object* v_base_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Elab_Do_ControlStack_mkContinue(v_base_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec_ref(v_a_2132_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn(lean_object* v_base_2149_, lean_object* v_r_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_m_2159_; lean_object* v_runInBase_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2206_; 
v_m_2159_ = lean_ctor_get(v_base_2149_, 1);
v_runInBase_2160_ = lean_ctor_get(v_base_2149_, 3);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_base_2149_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; lean_object* v_unused_2208_; lean_object* v_unused_2209_; 
v_unused_2207_ = lean_ctor_get(v_base_2149_, 4);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_base_2149_, 2);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_base_2149_, 0);
lean_dec(v_unused_2209_);
v___x_2162_ = v_base_2149_;
v_isShared_2163_ = v_isSharedCheck_2206_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_runInBase_2160_);
lean_inc(v_m_2159_);
lean_dec(v_base_2149_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2206_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; 
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc(v_a_2153_);
lean_inc_ref(v_a_2152_);
lean_inc_ref(v_a_2151_);
v___x_2164_ = lean_apply_8(v_m_2159_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, lean_box(0));
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_monadInfo_2165_; lean_object* v_a_2166_; lean_object* v_doBlockResultType_2167_; lean_object* v_u_2168_; lean_object* v_v_2169_; lean_object* v_cachedPUnit_2170_; lean_object* v_cachedPUnitUnit_2171_; lean_object* v___x_2173_; 
v_monadInfo_2165_ = lean_ctor_get(v_a_2151_, 0);
v_a_2166_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_n(v_a_2166_, 2);
lean_dec_ref(v___x_2164_);
v_doBlockResultType_2167_ = lean_ctor_get(v_a_2151_, 3);
v_u_2168_ = lean_ctor_get(v_monadInfo_2165_, 1);
v_v_2169_ = lean_ctor_get(v_monadInfo_2165_, 2);
v_cachedPUnit_2170_ = lean_ctor_get(v_monadInfo_2165_, 3);
v_cachedPUnitUnit_2171_ = lean_ctor_get(v_monadInfo_2165_, 4);
lean_inc_ref(v_cachedPUnitUnit_2171_);
lean_inc_ref(v_cachedPUnit_2170_);
lean_inc(v_v_2169_);
lean_inc(v_u_2168_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_cachedPUnitUnit_2171_);
lean_ctor_set(v___x_2162_, 3, v_cachedPUnit_2170_);
lean_ctor_set(v___x_2162_, 2, v_v_2169_);
lean_ctor_set(v___x_2162_, 1, v_u_2168_);
lean_ctor_set(v___x_2162_, 0, v_a_2166_);
v___x_2173_ = v___x_2162_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2166_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_u_2168_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2169_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_cachedPUnit_2170_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_cachedPUnitUnit_2171_);
v___x_2173_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; 
v___x_2174_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2173_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc_ref(v_r_2150_);
v___x_2176_ = lean_infer_type(v_r_2150_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v___x_2178_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1));
v___x_2179_ = 0;
v___x_2180_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_2178_, v___x_2179_, v_a_2151_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
lean_inc_ref(v_doBlockResultType_2167_);
v___x_2182_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2167_, v_a_2151_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1));
v___x_2185_ = lean_box(0);
lean_inc(v_v_2169_);
v___x_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_v_2169_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
lean_inc(v_u_2168_);
v___x_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_u_2168_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
lean_inc_ref(v___x_2187_);
v___x_2188_ = l_Lean_mkConst(v___x_2184_, v___x_2187_);
lean_inc(v_a_2181_);
lean_inc(v_a_2177_);
v___x_2189_ = l_Lean_mkAppB(v___x_2188_, v_a_2177_, v_a_2181_);
lean_inc(v_a_2166_);
v___x_2190_ = l_Lean_Expr_app___override(v_a_2166_, v___x_2189_);
v___x_2191_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2));
v___x_2192_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_2191_, v_a_2183_, v___x_2190_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v___x_2192_);
v___x_2193_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4));
v___x_2194_ = l_Lean_mkConst(v___x_2193_, v___x_2187_);
v___x_2195_ = l_Lean_mkApp5(v___x_2194_, v_a_2177_, v_a_2166_, v_a_2181_, v_a_2175_, v_r_2150_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc(v_a_2153_);
lean_inc_ref(v_a_2152_);
lean_inc_ref(v_a_2151_);
v___x_2196_ = lean_apply_9(v_runInBase_2160_, v___x_2195_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, lean_box(0));
return v___x_2196_;
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___x_2187_);
lean_dec(v_a_2181_);
lean_dec(v_a_2177_);
lean_dec(v_a_2175_);
lean_dec(v_a_2166_);
lean_dec_ref(v_runInBase_2160_);
lean_dec_ref(v_r_2150_);
v_a_2197_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2192_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2192_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_dec(v_a_2181_);
lean_dec(v_a_2177_);
lean_dec(v_a_2175_);
lean_dec(v_a_2166_);
lean_dec_ref(v_runInBase_2160_);
lean_dec_ref(v_r_2150_);
return v___x_2182_;
}
}
else
{
lean_dec(v_a_2177_);
lean_dec(v_a_2175_);
lean_dec(v_a_2166_);
lean_dec_ref(v_runInBase_2160_);
lean_dec_ref(v_r_2150_);
return v___x_2180_;
}
}
else
{
lean_dec(v_a_2175_);
lean_dec(v_a_2166_);
lean_dec_ref(v_runInBase_2160_);
lean_dec_ref(v_r_2150_);
return v___x_2176_;
}
}
else
{
lean_dec(v_a_2166_);
lean_dec_ref(v_runInBase_2160_);
lean_dec_ref(v_r_2150_);
return v___x_2174_;
}
}
}
else
{
lean_del_object(v___x_2162_);
lean_dec_ref(v_runInBase_2160_);
lean_dec_ref(v_r_2150_);
return v___x_2164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkReturn___boxed(lean_object* v_base_2210_, lean_object* v_r_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_Do_ControlStack_mkReturn(v_base_2210_, v_r_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec_ref(v_a_2212_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure(lean_object* v_base_2235_, lean_object* v_resultName_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_m_2245_; lean_object* v_runInBase_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2279_; 
v_m_2245_ = lean_ctor_get(v_base_2235_, 1);
v_runInBase_2246_ = lean_ctor_get(v_base_2235_, 3);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_base_2235_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; lean_object* v_unused_2281_; lean_object* v_unused_2282_; 
v_unused_2280_ = lean_ctor_get(v_base_2235_, 4);
lean_dec(v_unused_2280_);
v_unused_2281_ = lean_ctor_get(v_base_2235_, 2);
lean_dec(v_unused_2281_);
v_unused_2282_ = lean_ctor_get(v_base_2235_, 0);
lean_dec(v_unused_2282_);
v___x_2248_ = v_base_2235_;
v_isShared_2249_ = v_isSharedCheck_2279_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_runInBase_2246_);
lean_inc(v_m_2245_);
lean_dec(v_base_2235_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2279_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; 
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_a_2240_);
lean_inc(v_a_2239_);
lean_inc_ref(v_a_2238_);
lean_inc_ref(v_a_2237_);
v___x_2250_ = lean_apply_8(v_m_2245_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, lean_box(0));
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_monadInfo_2251_; lean_object* v_a_2252_; lean_object* v_u_2253_; lean_object* v_v_2254_; lean_object* v_cachedPUnit_2255_; lean_object* v_cachedPUnitUnit_2256_; lean_object* v___x_2258_; 
v_monadInfo_2251_ = lean_ctor_get(v_a_2237_, 0);
v_a_2252_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_n(v_a_2252_, 2);
lean_dec_ref(v___x_2250_);
v_u_2253_ = lean_ctor_get(v_monadInfo_2251_, 1);
v_v_2254_ = lean_ctor_get(v_monadInfo_2251_, 2);
v_cachedPUnit_2255_ = lean_ctor_get(v_monadInfo_2251_, 3);
v_cachedPUnitUnit_2256_ = lean_ctor_get(v_monadInfo_2251_, 4);
lean_inc_ref(v_cachedPUnitUnit_2256_);
lean_inc_ref(v_cachedPUnit_2255_);
lean_inc(v_v_2254_);
lean_inc(v_u_2253_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 4, v_cachedPUnitUnit_2256_);
lean_ctor_set(v___x_2248_, 3, v_cachedPUnit_2255_);
lean_ctor_set(v___x_2248_, 2, v_v_2254_);
lean_ctor_set(v___x_2248_, 1, v_u_2253_);
lean_ctor_set(v___x_2248_, 0, v_a_2252_);
v___x_2258_ = v___x_2248_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2252_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_u_2253_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_v_2254_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v_cachedPUnit_2255_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v_cachedPUnitUnit_2256_);
v___x_2258_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(v___x_2258_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = l_Lean_Meta_getFVarFromUserName(v_resultName_2236_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_n(v_a_2262_, 2);
lean_dec_ref(v___x_2261_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_a_2240_);
v___x_2263_ = lean_infer_type(v_a_2262_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__2));
v___x_2266_ = lean_box(0);
lean_inc(v_v_2254_);
v___x_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_v_2254_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
lean_inc(v_u_2253_);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_u_2253_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
lean_inc_ref_n(v___x_2268_, 2);
v___x_2269_ = l_Lean_mkConst(v___x_2265_, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__4));
v___x_2271_ = l_Lean_mkConst(v___x_2270_, v___x_2268_);
lean_inc_n(v_a_2252_, 2);
v___x_2272_ = l_Lean_mkAppB(v___x_2271_, v_a_2252_, v_a_2260_);
v___x_2273_ = l_Lean_mkAppB(v___x_2269_, v_a_2252_, v___x_2272_);
v___x_2274_ = ((lean_object*)(l_Lean_Elab_Do_ControlStack_mkPure___closed__7));
v___x_2275_ = l_Lean_mkConst(v___x_2274_, v___x_2268_);
v___x_2276_ = l_Lean_mkApp4(v___x_2275_, v_a_2252_, v___x_2273_, v_a_2264_, v_a_2262_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_a_2240_);
lean_inc(v_a_2239_);
lean_inc_ref(v_a_2238_);
lean_inc_ref(v_a_2237_);
v___x_2277_ = lean_apply_9(v_runInBase_2246_, v___x_2276_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, lean_box(0));
return v___x_2277_;
}
else
{
lean_dec(v_a_2262_);
lean_dec(v_a_2260_);
lean_dec(v_a_2252_);
lean_dec_ref(v_runInBase_2246_);
return v___x_2263_;
}
}
else
{
lean_dec(v_a_2260_);
lean_dec(v_a_2252_);
lean_dec_ref(v_runInBase_2246_);
return v___x_2261_;
}
}
else
{
lean_dec(v_a_2252_);
lean_dec_ref(v_runInBase_2246_);
lean_dec(v_resultName_2236_);
return v___x_2259_;
}
}
}
else
{
lean_del_object(v___x_2248_);
lean_dec_ref(v_runInBase_2246_);
lean_dec(v_resultName_2236_);
return v___x_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlStack_mkPure___boxed(lean_object* v_base_2283_, lean_object* v_resultName_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Elab_Do_ControlStack_mkPure(v_base_2283_, v_resultName_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(lean_object* v_info_2294_, lean_object* v_as_2295_, size_t v_i_2296_, size_t v_stop_2297_, lean_object* v_b_2298_){
_start:
{
lean_object* v___y_2300_; uint8_t v___x_2304_; 
v___x_2304_ = lean_usize_dec_eq(v_i_2296_, v_stop_2297_);
if (v___x_2304_ == 0)
{
lean_object* v_reassigns_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_reassigns_2305_ = lean_ctor_get(v_info_2294_, 1);
v___x_2306_ = lean_array_uget_borrowed(v_as_2295_, v_i_2296_);
v___x_2307_ = l_Lean_TSyntax_getId(v___x_2306_);
v___x_2308_ = l_Lean_NameSet_contains(v_reassigns_2305_, v___x_2307_);
lean_dec(v___x_2307_);
if (v___x_2308_ == 0)
{
v___y_2300_ = v_b_2298_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2309_; 
lean_inc(v___x_2306_);
v___x_2309_ = lean_array_push(v_b_2298_, v___x_2306_);
v___y_2300_ = v___x_2309_;
goto v___jp_2299_;
}
}
else
{
return v_b_2298_;
}
v___jp_2299_:
{
size_t v___x_2301_; size_t v___x_2302_; 
v___x_2301_ = ((size_t)1ULL);
v___x_2302_ = lean_usize_add(v_i_2296_, v___x_2301_);
v_i_2296_ = v___x_2302_;
v_b_2298_ = v___y_2300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0___boxed(lean_object* v_info_2310_, lean_object* v_as_2311_, lean_object* v_i_2312_, lean_object* v_stop_2313_, lean_object* v_b_2314_){
_start:
{
size_t v_i_boxed_2315_; size_t v_stop_boxed_2316_; lean_object* v_res_2317_; 
v_i_boxed_2315_ = lean_unbox_usize(v_i_2312_);
lean_dec(v_i_2312_);
v_stop_boxed_2316_ = lean_unbox_usize(v_stop_2313_);
lean_dec(v_stop_2313_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(v_info_2310_, v_as_2311_, v_i_boxed_2315_, v_stop_boxed_2316_, v_b_2314_);
lean_dec_ref(v_as_2311_);
lean_dec_ref(v_info_2310_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_ofCont(lean_object* v_info_2320_, lean_object* v_dec_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; uint8_t v___y_2336_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v_continueBase_x3f_2342_; lean_object* v_controlStack_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v_monadInfo_2367_; lean_object* v_mutVars_2368_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; lean_object* v_breakBase_x3f_2373_; lean_object* v_controlStack_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; uint8_t v___y_2385_; lean_object* v___y_2386_; uint8_t v___y_2387_; lean_object* v___y_2388_; lean_object* v_controlStack_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; uint8_t v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; uint8_t v___y_2403_; lean_object* v_returnBase_x3f_2404_; lean_object* v_controlStack_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2418_; uint8_t v___y_2419_; uint8_t v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2434_; uint8_t v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; uint8_t v___y_2438_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2483_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v_monadInfo_2367_ = lean_ctor_get(v_a_2322_, 0);
v_mutVars_2368_ = lean_ctor_get(v_a_2322_, 1);
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = lean_array_get_size(v_mutVars_2368_);
v___x_2526_ = ((lean_object*)(l_Lean_Elab_Do_ControlLifter_ofCont___closed__0));
v___x_2527_ = lean_nat_dec_lt(v___x_2524_, v___x_2525_);
if (v___x_2527_ == 0)
{
v___y_2483_ = v___x_2526_;
goto v___jp_2482_;
}
else
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_nat_dec_le(v___x_2525_, v___x_2525_);
if (v___x_2528_ == 0)
{
if (v___x_2527_ == 0)
{
v___y_2483_ = v___x_2526_;
goto v___jp_2482_;
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2525_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(v_info_2320_, v_mutVars_2368_, v___x_2529_, v___x_2530_, v___x_2526_);
v___y_2483_ = v___x_2531_;
goto v___jp_2482_;
}
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2525_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(v_info_2320_, v_mutVars_2368_, v___x_2532_, v___x_2533_, v___x_2526_);
v___y_2483_ = v___x_2534_;
goto v___jp_2482_;
}
}
v___jp_2330_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2337_, 0, v_dec_2321_);
lean_ctor_set(v___x_2337_, 1, v___y_2335_);
lean_ctor_set(v___x_2337_, 2, v___y_2334_);
lean_ctor_set(v___x_2337_, 3, v___y_2331_);
lean_ctor_set(v___x_2337_, 4, v___y_2332_);
lean_ctor_set(v___x_2337_, 5, v___y_2333_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*6, v___y_2336_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
return v___x_2338_;
}
v___jp_2339_:
{
lean_object* v_stM_2351_; lean_object* v_resultType_2352_; lean_object* v___x_2353_; 
v_stM_2351_ = lean_ctor_get(v_controlStack_2343_, 2);
v_resultType_2352_ = lean_ctor_get(v_dec_2321_, 1);
lean_inc_ref(v_stM_2351_);
lean_inc(v___y_2350_);
lean_inc_ref(v___y_2349_);
lean_inc(v___y_2348_);
lean_inc_ref(v___y_2347_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc_ref(v_resultType_2352_);
v___x_2353_ = lean_apply_9(v_stM_2351_, v_resultType_2352_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, lean_box(0));
if (lean_obj_tag(v___x_2353_) == 0)
{
uint8_t v_noFallthrough_2354_; 
v_noFallthrough_2354_ = lean_ctor_get_uint8(v_info_2320_, sizeof(void*)*2 + 3);
if (v_noFallthrough_2354_ == 0)
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2353_);
v___x_2356_ = 2;
v___y_2331_ = v_continueBase_x3f_2342_;
v___y_2332_ = v_controlStack_2343_;
v___y_2333_ = v_a_2355_;
v___y_2334_ = v___y_2341_;
v___y_2335_ = v___y_2340_;
v___y_2336_ = v___x_2356_;
goto v___jp_2330_;
}
else
{
lean_object* v_a_2357_; uint8_t v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2353_);
v___x_2358_ = 1;
v___y_2331_ = v_continueBase_x3f_2342_;
v___y_2332_ = v_controlStack_2343_;
v___y_2333_ = v_a_2357_;
v___y_2334_ = v___y_2341_;
v___y_2335_ = v___y_2340_;
v___y_2336_ = v___x_2358_;
goto v___jp_2330_;
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v_controlStack_2343_);
lean_dec(v_continueBase_x3f_2342_);
lean_dec(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v_dec_2321_);
v_a_2359_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2353_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2353_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
v___jp_2369_:
{
if (v___y_2371_ == 0)
{
v___y_2340_ = v___y_2372_;
v___y_2341_ = v_breakBase_x3f_2373_;
v_continueBase_x3f_2342_ = v___y_2370_;
v_controlStack_2343_ = v_controlStack_2374_;
v___y_2344_ = v___y_2375_;
v___y_2345_ = v___y_2376_;
v___y_2346_ = v___y_2377_;
v___y_2347_ = v___y_2378_;
v___y_2348_ = v___y_2379_;
v___y_2349_ = v___y_2380_;
v___y_2350_ = v___y_2381_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v___y_2370_);
lean_inc_ref(v_controlStack_2374_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_controlStack_2374_);
lean_inc_ref(v_monadInfo_2367_);
v___x_2383_ = l_Lean_Elab_Do_ControlStack_continueT(v_monadInfo_2367_, v_controlStack_2374_);
v___y_2340_ = v___y_2372_;
v___y_2341_ = v_breakBase_x3f_2373_;
v_continueBase_x3f_2342_ = v___x_2382_;
v_controlStack_2343_ = v___x_2383_;
v___y_2344_ = v___y_2375_;
v___y_2345_ = v___y_2376_;
v___y_2346_ = v___y_2377_;
v___y_2347_ = v___y_2378_;
v___y_2348_ = v___y_2379_;
v___y_2349_ = v___y_2380_;
v___y_2350_ = v___y_2381_;
goto v___jp_2339_;
}
}
v___jp_2384_:
{
if (v___y_2385_ == 0)
{
lean_inc(v___y_2386_);
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2387_;
v___y_2372_ = v___y_2388_;
v_breakBase_x3f_2373_ = v___y_2386_;
v_controlStack_2374_ = v_controlStack_2389_;
v___y_2375_ = v___y_2390_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2392_;
v___y_2378_ = v___y_2393_;
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___y_2396_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_inc_ref(v_controlStack_2389_);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_controlStack_2389_);
lean_inc_ref(v_monadInfo_2367_);
v___x_2398_ = l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_2367_, v_controlStack_2389_);
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2387_;
v___y_2372_ = v___y_2388_;
v_breakBase_x3f_2373_ = v___x_2397_;
v_controlStack_2374_ = v___x_2398_;
v___y_2375_ = v___y_2390_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2392_;
v___y_2378_ = v___y_2393_;
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2395_;
v___y_2381_ = v___y_2396_;
goto v___jp_2369_;
}
}
v___jp_2399_:
{
if (lean_obj_tag(v___y_2401_) == 1)
{
lean_object* v_val_2413_; lean_object* v_fst_2414_; lean_object* v_snd_2415_; lean_object* v___x_2416_; 
v_val_2413_ = lean_ctor_get(v___y_2401_, 0);
lean_inc(v_val_2413_);
lean_dec_ref(v___y_2401_);
v_fst_2414_ = lean_ctor_get(v_val_2413_, 0);
lean_inc(v_fst_2414_);
v_snd_2415_ = lean_ctor_get(v_val_2413_, 1);
lean_inc(v_snd_2415_);
lean_dec(v_val_2413_);
lean_inc_ref(v_monadInfo_2367_);
v___x_2416_ = l_Lean_Elab_Do_ControlStack_stateT(v_monadInfo_2367_, v_fst_2414_, v_snd_2415_, v_controlStack_2405_);
v___y_2385_ = v___y_2400_;
v___y_2386_ = v___y_2402_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v_returnBase_x3f_2404_;
v_controlStack_2389_ = v___x_2416_;
v___y_2390_ = v___y_2406_;
v___y_2391_ = v___y_2407_;
v___y_2392_ = v___y_2408_;
v___y_2393_ = v___y_2409_;
v___y_2394_ = v___y_2410_;
v___y_2395_ = v___y_2411_;
v___y_2396_ = v___y_2412_;
goto v___jp_2384_;
}
else
{
lean_dec(v___y_2401_);
v___y_2385_ = v___y_2400_;
v___y_2386_ = v___y_2402_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v_returnBase_x3f_2404_;
v_controlStack_2389_ = v_controlStack_2405_;
v___y_2390_ = v___y_2406_;
v___y_2391_ = v___y_2407_;
v___y_2392_ = v___y_2408_;
v___y_2393_ = v___y_2409_;
v___y_2394_ = v___y_2410_;
v___y_2395_ = v___y_2411_;
v___y_2396_ = v___y_2412_;
goto v___jp_2384_;
}
}
v___jp_2417_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_box(0);
lean_inc_ref(v_monadInfo_2367_);
v___x_2423_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_2367_);
if (lean_obj_tag(v___y_2418_) == 1)
{
lean_object* v_val_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2432_; 
v_val_2424_ = lean_ctor_get(v___y_2418_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___y_2418_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2426_ = v___y_2418_;
v_isShared_2427_ = v_isSharedCheck_2432_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_val_2424_);
lean_dec(v___y_2418_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2432_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
lean_inc_ref(v___x_2423_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2423_);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2423_);
v___x_2429_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; 
lean_inc_ref(v_monadInfo_2367_);
v___x_2430_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(v_monadInfo_2367_, v_val_2424_, v___x_2423_);
v___y_2400_ = v___y_2419_;
v___y_2401_ = v___y_2421_;
v___y_2402_ = v___x_2422_;
v___y_2403_ = v___y_2420_;
v_returnBase_x3f_2404_ = v___x_2429_;
v_controlStack_2405_ = v___x_2430_;
v___y_2406_ = v_a_2322_;
v___y_2407_ = v_a_2323_;
v___y_2408_ = v_a_2324_;
v___y_2409_ = v_a_2325_;
v___y_2410_ = v_a_2326_;
v___y_2411_ = v_a_2327_;
v___y_2412_ = v_a_2328_;
goto v___jp_2399_;
}
}
}
else
{
lean_dec(v___y_2418_);
v___y_2400_ = v___y_2419_;
v___y_2401_ = v___y_2421_;
v___y_2402_ = v___x_2422_;
v___y_2403_ = v___y_2420_;
v_returnBase_x3f_2404_ = v___x_2422_;
v_controlStack_2405_ = v___x_2423_;
v___y_2406_ = v_a_2322_;
v___y_2407_ = v_a_2323_;
v___y_2408_ = v_a_2324_;
v___y_2409_ = v_a_2325_;
v___y_2410_ = v_a_2326_;
v___y_2411_ = v_a_2327_;
v___y_2412_ = v_a_2328_;
goto v___jp_2399_;
}
}
v___jp_2433_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2439_ = lean_array_get_size(v___y_2437_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = lean_nat_dec_eq(v___x_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___y_2437_);
lean_ctor_set(v___x_2442_, 1, v___y_2436_);
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
v___y_2418_ = v___y_2434_;
v___y_2419_ = v___y_2435_;
v___y_2420_ = v___y_2438_;
v___y_2421_ = v___x_2443_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2444_; 
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2436_);
v___x_2444_ = lean_box(0);
v___y_2418_ = v___y_2434_;
v___y_2419_ = v___y_2435_;
v___y_2420_ = v___y_2438_;
v___y_2421_ = v___x_2444_;
goto v___jp_2417_;
}
}
v___jp_2445_:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2322_);
if (lean_obj_tag(v___x_2450_) == 0)
{
uint8_t v_continues_2451_; 
v_continues_2451_ = lean_ctor_get_uint8(v_info_2320_, sizeof(void*)*2 + 1);
if (v_continues_2451_ == 0)
{
lean_dec_ref(v___x_2450_);
v___y_2434_ = v___y_2446_;
v___y_2435_ = v___y_2449_;
v___y_2436_ = v___y_2447_;
v___y_2437_ = v___y_2448_;
v___y_2438_ = v_continues_2451_;
goto v___jp_2433_;
}
else
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2452_);
lean_dec_ref(v___x_2450_);
if (lean_obj_tag(v_a_2452_) == 0)
{
uint8_t v___x_2453_; 
v___x_2453_ = 0;
v___y_2434_ = v___y_2446_;
v___y_2435_ = v___y_2449_;
v___y_2436_ = v___y_2447_;
v___y_2437_ = v___y_2448_;
v___y_2438_ = v___x_2453_;
goto v___jp_2433_;
}
else
{
lean_dec_ref(v_a_2452_);
v___y_2434_ = v___y_2446_;
v___y_2435_ = v___y_2449_;
v___y_2436_ = v___y_2447_;
v___y_2437_ = v___y_2448_;
v___y_2438_ = v_continues_2451_;
goto v___jp_2433_;
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v_dec_2321_);
v_a_2454_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2450_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2450_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
v___jp_2462_:
{
uint8_t v___x_2466_; 
v___x_2466_ = 0;
v___y_2446_ = v___y_2463_;
v___y_2447_ = v___y_2464_;
v___y_2448_ = v___y_2465_;
v___y_2449_ = v___x_2466_;
goto v___jp_2445_;
}
v___jp_2467_:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2322_);
if (lean_obj_tag(v___x_2471_) == 0)
{
uint8_t v_breaks_2472_; 
v_breaks_2472_ = lean_ctor_get_uint8(v_info_2320_, sizeof(void*)*2);
if (v_breaks_2472_ == 0)
{
lean_dec_ref(v___x_2471_);
v___y_2463_ = v___y_2470_;
v___y_2464_ = v___y_2468_;
v___y_2465_ = v___y_2469_;
goto v___jp_2462_;
}
else
{
lean_object* v_a_2473_; 
v_a_2473_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2471_);
if (lean_obj_tag(v_a_2473_) == 0)
{
v___y_2463_ = v___y_2470_;
v___y_2464_ = v___y_2468_;
v___y_2465_ = v___y_2469_;
goto v___jp_2462_;
}
else
{
lean_dec_ref(v_a_2473_);
v___y_2446_ = v___y_2470_;
v___y_2447_ = v___y_2468_;
v___y_2448_ = v___y_2469_;
v___y_2449_ = v_breaks_2472_;
goto v___jp_2445_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec_ref(v_dec_2321_);
v_a_2474_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2471_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2471_);
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
v___jp_2482_:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2322_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; size_t v_sz_2489_; lean_object* v___x_2490_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref(v___x_2484_);
v_sz_2486_ = lean_array_size(v___y_2483_);
v___x_2487_ = ((size_t)0ULL);
lean_inc_ref(v___y_2483_);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_2486_, v___x_2487_, v___y_2483_);
v_sz_2489_ = lean_array_size(v___x_2488_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_2489_, v___x_2487_, v___x_2488_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v_u_2492_; lean_object* v___x_2493_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref(v___x_2490_);
v_u_2492_ = lean_ctor_get(v_monadInfo_2367_, 1);
lean_inc(v_u_2492_);
v___x_2493_ = l_Lean_Meta_mkProdN(v_a_2491_, v_u_2492_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2493_) == 0)
{
uint8_t v_returnsEarly_2494_; 
v_returnsEarly_2494_ = lean_ctor_get_uint8(v_info_2320_, sizeof(void*)*2 + 2);
if (v_returnsEarly_2494_ == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; 
lean_dec(v_a_2485_);
v_a_2495_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2493_);
v___x_2496_ = lean_box(0);
v___y_2468_ = v_a_2495_;
v___y_2469_ = v___y_2483_;
v___y_2470_ = v___x_2496_;
goto v___jp_2467_;
}
else
{
lean_object* v_a_2497_; lean_object* v_resultType_2498_; lean_object* v___x_2499_; 
v_a_2497_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2493_);
v_resultType_2498_ = lean_ctor_get(v_a_2485_, 0);
lean_inc_ref(v_resultType_2498_);
lean_dec(v_a_2485_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_resultType_2498_);
v___y_2468_ = v_a_2497_;
v___y_2469_ = v___y_2483_;
v___y_2470_ = v___x_2499_;
goto v___jp_2467_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_a_2485_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_dec_2321_);
v_a_2500_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2493_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2493_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2485_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_dec_2321_);
v_a_2508_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2490_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2490_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_dec_2321_);
v_a_2516_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2484_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2484_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_ofCont___boxed(lean_object* v_info_2535_, lean_object* v_dec_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Elab_Do_ControlLifter_ofCont(v_info_2535_, v_dec_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec_ref(v_info_2535_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_lift(lean_object* v_l_2546_, lean_object* v_elabElem_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_2548_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2556_);
v___x_2558_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_2548_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2558_);
v___x_2560_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_2548_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2615_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref(v___x_2560_);
if (lean_obj_tag(v_a_2557_) == 1)
{
lean_object* v_breakBase_x3f_2626_; 
v_breakBase_x3f_2626_ = lean_ctor_get(v_l_2546_, 2);
lean_inc(v_breakBase_x3f_2626_);
if (lean_obj_tag(v_breakBase_x3f_2626_) == 1)
{
lean_object* v_continueBase_x3f_2627_; lean_object* v_val_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v_a_2557_);
v_continueBase_x3f_2627_ = lean_ctor_get(v_l_2546_, 3);
v_val_2628_ = lean_ctor_get(v_breakBase_x3f_2626_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_breakBase_x3f_2626_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2630_ = v_breakBase_x3f_2626_;
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_val_2628_);
lean_dec(v_breakBase_x3f_2626_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
uint8_t v___y_2633_; 
if (lean_obj_tag(v_continueBase_x3f_2627_) == 0)
{
uint8_t v___x_2639_; 
v___x_2639_ = 0;
v___y_2633_ = v___x_2639_;
goto v___jp_2632_;
}
else
{
uint8_t v___x_2640_; 
v___x_2640_ = 1;
v___y_2633_ = v___x_2640_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2634_ = lean_box(v___y_2633_);
v___x_2635_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkBreak___boxed), 10, 2);
lean_closure_set(v___x_2635_, 0, v_val_2628_);
lean_closure_set(v___x_2635_, 1, v___x_2634_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2635_);
v___x_2637_ = v___x_2630_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
v___y_2615_ = v___x_2637_;
goto v___jp_2614_;
}
}
}
}
else
{
lean_dec(v_breakBase_x3f_2626_);
v___y_2615_ = v_a_2557_;
goto v___jp_2614_;
}
}
else
{
v___y_2615_ = v_a_2557_;
goto v___jp_2614_;
}
v___jp_2562_:
{
lean_object* v_origCont_2566_; lean_object* v_pureBase_2567_; lean_object* v_liftedDoBlockResultType_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2595_; 
v_origCont_2566_ = lean_ctor_get(v_l_2546_, 0);
v_pureBase_2567_ = lean_ctor_get(v_l_2546_, 4);
v_liftedDoBlockResultType_2568_ = lean_ctor_get(v_l_2546_, 5);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_l_2546_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; lean_object* v_unused_2597_; lean_object* v_unused_2598_; 
v_unused_2596_ = lean_ctor_get(v_l_2546_, 3);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_l_2546_, 2);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_l_2546_, 1);
lean_dec(v_unused_2598_);
v___x_2570_ = v_l_2546_;
v_isShared_2571_ = v_isSharedCheck_2595_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_liftedDoBlockResultType_2568_);
lean_inc(v_pureBase_2567_);
lean_inc(v_origCont_2566_);
lean_dec(v_l_2546_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2595_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_resultName_2572_; lean_object* v_resultType_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2593_; 
v_resultName_2572_ = lean_ctor_get(v_origCont_2566_, 0);
v_resultType_2573_ = lean_ctor_get(v_origCont_2566_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_origCont_2566_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; 
v_unused_2594_ = lean_ctor_get(v_origCont_2566_, 2);
lean_dec(v_unused_2594_);
v___x_2575_ = v_origCont_2566_;
v_isShared_2576_ = v_isSharedCheck_2593_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_resultType_2573_);
lean_inc(v_resultName_2572_);
lean_dec(v_origCont_2566_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2593_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_monadInfo_2577_; lean_object* v_mutVars_2578_; lean_object* v_mutVarDefs_2579_; uint8_t v_deadCode_2580_; lean_object* v_ops_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2587_; 
v_monadInfo_2577_ = lean_ctor_get(v_a_2548_, 0);
v_mutVars_2578_ = lean_ctor_get(v_a_2548_, 1);
v_mutVarDefs_2579_ = lean_ctor_get(v_a_2548_, 2);
v_deadCode_2580_ = lean_ctor_get_uint8(v_a_2548_, sizeof(void*)*6);
v_ops_2581_ = lean_ctor_get(v_a_2548_, 5);
lean_inc(v_resultName_2572_);
v___x_2582_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkPure___boxed), 10, 2);
lean_closure_set(v___x_2582_, 0, v_pureBase_2567_);
lean_closure_set(v___x_2582_, 1, v_resultName_2572_);
v___x_2583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2565_);
lean_ctor_set(v___x_2583_, 1, v___y_2563_);
lean_ctor_set(v___x_2583_, 2, v___y_2564_);
v___x_2584_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_2583_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = 1;
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 2, v___x_2582_);
v___x_2587_ = v___x_2575_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_resultName_2572_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_resultType_2573_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v___x_2582_);
v___x_2587_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*3, v___x_2585_);
lean_inc(v_ops_2581_);
lean_inc_ref(v_mutVarDefs_2579_);
lean_inc_ref(v_mutVars_2578_);
lean_inc_ref(v_monadInfo_2577_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 5, v_ops_2581_);
lean_ctor_set(v___x_2570_, 4, v___x_2584_);
lean_ctor_set(v___x_2570_, 3, v_liftedDoBlockResultType_2568_);
lean_ctor_set(v___x_2570_, 2, v_mutVarDefs_2579_);
lean_ctor_set(v___x_2570_, 1, v_mutVars_2578_);
lean_ctor_set(v___x_2570_, 0, v_monadInfo_2577_);
v___x_2589_ = v___x_2570_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_monadInfo_2577_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_mutVars_2578_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_mutVarDefs_2579_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_liftedDoBlockResultType_2568_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2591_, 5, v_ops_2581_);
v___x_2589_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; 
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*6, v_deadCode_2580_);
lean_inc(v_a_2554_);
lean_inc_ref(v_a_2553_);
lean_inc(v_a_2552_);
lean_inc_ref(v_a_2551_);
lean_inc(v_a_2550_);
lean_inc_ref(v_a_2549_);
v___x_2590_ = lean_apply_9(v_elabElem_2547_, v___x_2587_, v___x_2589_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, lean_box(0));
return v___x_2590_;
}
}
}
}
}
v___jp_2599_:
{
lean_object* v_returnBase_x3f_2602_; 
v_returnBase_x3f_2602_ = lean_ctor_get(v_l_2546_, 1);
if (lean_obj_tag(v_returnBase_x3f_2602_) == 1)
{
lean_object* v_val_2603_; lean_object* v_resultType_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
v_val_2603_ = lean_ctor_get(v_returnBase_x3f_2602_, 0);
v_resultType_2604_ = lean_ctor_get(v_a_2561_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_a_2561_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; 
v_unused_2613_ = lean_ctor_get(v_a_2561_, 1);
lean_dec(v_unused_2613_);
v___x_2606_ = v_a_2561_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_resultType_2604_);
lean_dec(v_a_2561_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_inc(v_val_2603_);
v___x_2608_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkReturn___boxed), 10, 1);
lean_closure_set(v___x_2608_, 0, v_val_2603_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v___x_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_resultType_2604_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
v___y_2563_ = v___y_2600_;
v___y_2564_ = v___y_2601_;
v___y_2565_ = v___x_2610_;
goto v___jp_2562_;
}
}
}
else
{
v___y_2563_ = v___y_2600_;
v___y_2564_ = v___y_2601_;
v___y_2565_ = v_a_2561_;
goto v___jp_2562_;
}
}
v___jp_2614_:
{
if (lean_obj_tag(v_a_2559_) == 1)
{
lean_object* v_continueBase_x3f_2616_; 
v_continueBase_x3f_2616_ = lean_ctor_get(v_l_2546_, 3);
lean_inc(v_continueBase_x3f_2616_);
if (lean_obj_tag(v_continueBase_x3f_2616_) == 1)
{
lean_object* v_val_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v_a_2559_);
v_val_2617_ = lean_ctor_get(v_continueBase_x3f_2616_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_continueBase_x3f_2616_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2619_ = v_continueBase_x3f_2616_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_val_2617_);
lean_dec(v_continueBase_x3f_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_ControlStack_mkContinue___boxed), 9, 1);
lean_closure_set(v___x_2621_, 0, v_val_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
v___y_2600_ = v___y_2615_;
v___y_2601_ = v___x_2623_;
goto v___jp_2599_;
}
}
}
else
{
lean_dec(v_continueBase_x3f_2616_);
v___y_2600_ = v___y_2615_;
v___y_2601_ = v_a_2559_;
goto v___jp_2599_;
}
}
else
{
v___y_2600_ = v___y_2615_;
v___y_2601_ = v_a_2559_;
goto v___jp_2599_;
}
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_a_2559_);
lean_dec(v_a_2557_);
lean_dec_ref(v_elabElem_2547_);
lean_dec_ref(v_l_2546_);
v_a_2642_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2560_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2560_);
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
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v_a_2557_);
lean_dec_ref(v_elabElem_2547_);
lean_dec_ref(v_l_2546_);
v_a_2650_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2558_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2558_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref(v_elabElem_2547_);
lean_dec_ref(v_l_2546_);
v_a_2658_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2556_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2556_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_lift___boxed(lean_object* v_l_2666_, lean_object* v_elabElem_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Elab_Do_ControlLifter_lift(v_l_2666_, v_elabElem_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec_ref(v_a_2668_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_restoreCont(lean_object* v_l_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_pureBase_2686_; lean_object* v_origCont_2687_; uint8_t v_pureDeadCode_2688_; lean_object* v_restoreCont_2689_; lean_object* v_resultName_2690_; lean_object* v_resultType_2691_; lean_object* v_k_2692_; uint8_t v_kind_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2703_; 
v_pureBase_2686_ = lean_ctor_get(v_l_2677_, 4);
lean_inc_ref(v_pureBase_2686_);
v_origCont_2687_ = lean_ctor_get(v_l_2677_, 0);
lean_inc_ref(v_origCont_2687_);
v_pureDeadCode_2688_ = lean_ctor_get_uint8(v_l_2677_, sizeof(void*)*6);
lean_dec_ref(v_l_2677_);
v_restoreCont_2689_ = lean_ctor_get(v_pureBase_2686_, 4);
lean_inc_ref(v_restoreCont_2689_);
lean_dec_ref(v_pureBase_2686_);
v_resultName_2690_ = lean_ctor_get(v_origCont_2687_, 0);
v_resultType_2691_ = lean_ctor_get(v_origCont_2687_, 1);
v_k_2692_ = lean_ctor_get(v_origCont_2687_, 2);
v_kind_2693_ = lean_ctor_get_uint8(v_origCont_2687_, sizeof(void*)*3);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_origCont_2687_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2695_ = v_origCont_2687_;
v_isShared_2696_ = v_isSharedCheck_2703_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_k_2692_);
lean_inc(v_resultType_2691_);
lean_inc(v_resultName_2690_);
lean_dec(v_origCont_2687_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2703_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2697_ = lean_box(v_pureDeadCode_2688_);
v___x_2698_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_withDeadCode___boxed), 11, 3);
lean_closure_set(v___x_2698_, 0, lean_box(0));
lean_closure_set(v___x_2698_, 1, v___x_2697_);
lean_closure_set(v___x_2698_, 2, v_k_2692_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 2, v___x_2698_);
v___x_2700_ = v___x_2695_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_resultName_2690_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_resultType_2691_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v___x_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2702_, sizeof(void*)*3, v_kind_2693_);
v___x_2700_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; 
lean_inc(v_a_2684_);
lean_inc_ref(v_a_2683_);
lean_inc(v_a_2682_);
lean_inc_ref(v_a_2681_);
lean_inc(v_a_2680_);
lean_inc_ref(v_a_2679_);
lean_inc_ref(v_a_2678_);
v___x_2701_ = lean_apply_9(v_restoreCont_2689_, v___x_2700_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, lean_box(0));
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlLifter_restoreCont___boxed(lean_object* v_l_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Elab_Do_ControlLifter_restoreCont(v_l_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec_ref(v_a_2705_);
return v_res_2713_;
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
