// Lean compiler output
// Module: Lean.Elab.PreDefinition.MkInhabitant
// Imports: public import Lean.Meta.AppBuilder public import Lean.PrettyPrinter import Init.Omega
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(108, 140, 114, 129, 213, 60, 200, 249)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ", could not prove that the type"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "\nis nonempty.\n\nThis process uses multiple strategies:\n- It looks for a parameter that matches the return type.\n- It tries synthesizing '"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' and '"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "' instances for the return type, while making every parameter into a local '"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__11;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 182, .m_capacity = 182, .m_length = 181, .m_data = "' instance.\n- It tries unfolding the return type.\n\nIf the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it."};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_6(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_9_, lean_object* v_b_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_9_, v_b_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(lean_object* v_name_17_, lean_object* v_type_18_, lean_object* v_val_19_, lean_object* v_k_20_, uint8_t v_nondep_21_, uint8_t v_kind_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_28_, 0, v_k_20_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_17_, v_type_18_, v_val_19_, v___f_28_, v_nondep_21_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___boxed(lean_object* v_name_46_, lean_object* v_type_47_, lean_object* v_val_48_, lean_object* v_k_49_, lean_object* v_nondep_50_, lean_object* v_kind_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_nondep_boxed_57_; uint8_t v_kind_boxed_58_; lean_object* v_res_59_; 
v_nondep_boxed_57_ = lean_unbox(v_nondep_50_);
v_kind_boxed_58_ = lean_unbox(v_kind_51_);
v_res_59_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_46_, v_type_47_, v_val_48_, v_k_49_, v_nondep_boxed_57_, v_kind_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(lean_object* v_00_u03b1_60_, lean_object* v_name_61_, lean_object* v_type_62_, lean_object* v_val_63_, lean_object* v_k_64_, uint8_t v_nondep_65_, uint8_t v_kind_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_61_, v_type_62_, v_val_63_, v_k_64_, v_nondep_65_, v_kind_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(lean_object* v_00_u03b1_73_, lean_object* v_name_74_, lean_object* v_type_75_, lean_object* v_val_76_, lean_object* v_k_77_, lean_object* v_nondep_78_, lean_object* v_kind_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_nondep_boxed_85_; uint8_t v_kind_boxed_86_; lean_object* v_res_87_; 
v_nondep_boxed_85_ = lean_unbox(v_nondep_78_);
v_kind_boxed_86_ = lean_unbox(v_kind_79_);
v_res_87_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(v_00_u03b1_73_, v_name_74_, v_type_75_, v_val_76_, v_k_77_, v_nondep_boxed_85_, v_kind_boxed_86_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(lean_object* v_i_88_, lean_object* v_insts_89_, lean_object* v_xs_90_, lean_object* v_k_91_, lean_object* v_inst_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_88_, v_insts_89_, v_xs_90_, v_k_91_, v_inst_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v_i_88_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(lean_object* v_xs_109_, lean_object* v_k_110_, lean_object* v_i_111_, lean_object* v_insts_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_get_size(v_xs_109_);
v___x_119_ = lean_nat_dec_lt(v_i_111_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec(v_i_111_);
lean_dec_ref(v_xs_109_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
v___x_120_ = lean_apply_6(v_k_110_, v_insts_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, lean_box(0));
return v___x_120_;
}
else
{
lean_object* v_x_121_; lean_object* v___x_122_; 
v_x_121_ = lean_array_fget(v_xs_109_, v_i_111_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
lean_inc(v_x_121_);
v___x_122_ = lean_infer_type(v_x_121_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc_n(v_a_123_, 2);
lean_dec_ref(v___x_122_);
v___x_124_ = l_Lean_Meta_getLevel(v_a_123_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v___x_124_);
v___f_126_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_126_, 0, v_i_111_);
lean_closure_set(v___f_126_, 1, v_insts_112_);
lean_closure_set(v___f_126_, 2, v_xs_109_);
lean_closure_set(v___f_126_, 3, v_k_110_);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1));
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v_a_125_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_inc_ref(v___x_129_);
v___x_130_ = l_Lean_Expr_const___override(v___x_127_, v___x_129_);
lean_inc(v_a_123_);
v___x_131_ = l_Lean_Expr_app___override(v___x_130_, v_a_123_);
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3));
v___x_133_ = l_Lean_Expr_const___override(v___x_132_, v___x_129_);
v___x_134_ = l_Lean_mkAppB(v___x_133_, v_a_123_, v_x_121_);
v___x_135_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5));
v___x_136_ = 0;
v___x_137_ = 0;
v___x_138_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v___x_135_, v___x_131_, v___x_134_, v___f_126_, v___x_136_, v___x_137_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_123_);
lean_dec(v_x_121_);
lean_dec_ref(v_insts_112_);
lean_dec(v_i_111_);
lean_dec_ref(v_k_110_);
lean_dec_ref(v_xs_109_);
v_a_139_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_124_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_124_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_x_121_);
lean_dec_ref(v_insts_112_);
lean_dec(v_i_111_);
lean_dec_ref(v_k_110_);
lean_dec_ref(v_xs_109_);
v_a_147_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_122_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_122_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(lean_object* v_i_155_, lean_object* v_insts_156_, lean_object* v_xs_157_, lean_object* v_k_158_, lean_object* v_inst_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_155_, v___x_165_);
v___x_167_ = lean_array_push(v_insts_156_, v_inst_159_);
v___x_168_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_157_, v_k_158_, v___x_166_, v___x_167_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(lean_object* v_xs_169_, lean_object* v_k_170_, lean_object* v_i_171_, lean_object* v_insts_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_169_, v_k_170_, v_i_171_, v_insts_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(lean_object* v_00_u03b1_179_, lean_object* v_xs_180_, lean_object* v_k_181_, lean_object* v_i_182_, lean_object* v_insts_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_180_, v_k_181_, v_i_182_, v_insts_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(lean_object* v_00_u03b1_190_, lean_object* v_xs_191_, lean_object* v_k_192_, lean_object* v_i_193_, lean_object* v_insts_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(v_00_u03b1_190_, v_xs_191_, v_k_192_, v_i_193_, v_insts_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(lean_object* v_xs_203_, lean_object* v_k_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0));
v___x_212_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_203_, v_k_204_, v___x_210_, v___x_211_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(lean_object* v_xs_213_, lean_object* v_k_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_213_, v_k_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(lean_object* v_00_u03b1_221_, lean_object* v_xs_222_, lean_object* v_k_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_222_, v_k_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(lean_object* v_00_u03b1_230_, lean_object* v_xs_231_, lean_object* v_k_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(v_00_u03b1_230_, v_xs_231_, v_k_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object* v_type_239_, uint8_t v_useOfNonempty_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___y_247_; uint8_t v___y_248_; lean_object* v_a_253_; 
if (v_useOfNonempty_240_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_mkDefault(v_type_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; 
v_a_266_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_266_);
lean_dec_ref(v___x_256_);
v_a_253_ = v_a_266_;
goto v___jp_252_;
}
}
else
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Meta_mkOfNonempty(v_type_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_267_);
v_a_253_ = v_a_277_;
goto v___jp_252_;
}
}
v___jp_246_:
{
if (v___y_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v___y_247_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___y_247_);
return v___x_251_;
}
}
v___jp_252_:
{
uint8_t v___x_254_; 
v___x_254_ = l_Lean_Exception_isInterrupt(v_a_253_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
lean_inc_ref(v_a_253_);
v___x_255_ = l_Lean_Exception_isRuntime(v_a_253_);
v___y_247_ = v_a_253_;
v___y_248_ = v___x_255_;
goto v___jp_246_;
}
else
{
v___y_247_ = v_a_253_;
v___y_248_ = v___x_254_;
goto v___jp_246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object* v_type_278_, lean_object* v_useOfNonempty_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_useOfNonempty_boxed_285_; lean_object* v_res_286_; 
v_useOfNonempty_boxed_285_ = lean_unbox(v_useOfNonempty_279_);
v_res_286_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_278_, v_useOfNonempty_boxed_285_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(lean_object* v_k_287_, lean_object* v_b_288_, lean_object* v_c_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
v___x_295_ = lean_apply_7(v_k_287_, v_b_288_, v_c_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, lean_box(0));
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_k_296_, lean_object* v_b_297_, lean_object* v_c_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_296_, v_b_297_, v_c_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(lean_object* v_type_305_, lean_object* v_k_306_, uint8_t v_cleanupAnnotations_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___f_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_313_, 0, v_k_306_);
v___x_314_ = 0;
v___x_315_ = lean_box(0);
v___x_316_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_314_, v___x_315_, v_type_305_, v___f_313_, v_cleanupAnnotations_307_, v___x_314_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_a_325_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_316_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_316_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___boxed(lean_object* v_type_333_, lean_object* v_k_334_, lean_object* v_cleanupAnnotations_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_341_; lean_object* v_res_342_; 
v_cleanupAnnotations_boxed_341_ = lean_unbox(v_cleanupAnnotations_335_);
v_res_342_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_333_, v_k_334_, v_cleanupAnnotations_boxed_341_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(lean_object* v_00_u03b1_343_, lean_object* v_type_344_, lean_object* v_k_345_, uint8_t v_cleanupAnnotations_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_344_, v_k_345_, v_cleanupAnnotations_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(lean_object* v_00_u03b1_353_, lean_object* v_type_354_, lean_object* v_k_355_, lean_object* v_cleanupAnnotations_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_362_; lean_object* v_res_363_; 
v_cleanupAnnotations_boxed_362_ = lean_unbox(v_cleanupAnnotations_356_);
v_res_363_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(v_00_u03b1_353_, v_type_354_, v_k_355_, v_cleanupAnnotations_boxed_362_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_maxRecDepthErrorMessage;
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3);
v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4);
v___x_374_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2));
v___x_375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(lean_object* v_ref_376_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_ref_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(lean_object* v_ref_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(lean_object* v_00_u03b1_384_, lean_object* v_ref_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_385_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(lean_object* v_00_u03b1_392_, lean_object* v_ref_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(v_00_u03b1_392_, v_ref_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(lean_object* v_xs_400_, lean_object* v_insts_401_, lean_object* v_useOfNonempty_402_, lean_object* v_xs_x27_403_, lean_object* v_type_x27_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v_useOfNonempty_boxed_410_; lean_object* v_res_411_; 
v_useOfNonempty_boxed_410_ = lean_unbox(v_useOfNonempty_402_);
v_res_411_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_400_, v_insts_401_, v_useOfNonempty_boxed_410_, v_xs_x27_403_, v_type_x27_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(lean_object* v_xs_412_, lean_object* v_insts_413_, lean_object* v_type_414_, uint8_t v_useOfNonempty_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_fileName_421_; lean_object* v_fileMap_422_; lean_object* v_options_423_; lean_object* v_currRecDepth_424_; lean_object* v_maxRecDepth_425_; lean_object* v_ref_426_; lean_object* v_currNamespace_427_; lean_object* v_openDecls_428_; lean_object* v_initHeartbeats_429_; lean_object* v_maxHeartbeats_430_; lean_object* v_quotContext_431_; lean_object* v_currMacroScope_432_; uint8_t v_diag_433_; lean_object* v_cancelTk_x3f_434_; uint8_t v_suppressElabErrors_435_; lean_object* v_inheritedTraceOptions_436_; uint8_t v___x_437_; 
v_fileName_421_ = lean_ctor_get(v_a_418_, 0);
lean_inc_ref(v_fileName_421_);
v_fileMap_422_ = lean_ctor_get(v_a_418_, 1);
lean_inc_ref(v_fileMap_422_);
v_options_423_ = lean_ctor_get(v_a_418_, 2);
lean_inc_ref(v_options_423_);
v_currRecDepth_424_ = lean_ctor_get(v_a_418_, 3);
lean_inc(v_currRecDepth_424_);
v_maxRecDepth_425_ = lean_ctor_get(v_a_418_, 4);
lean_inc(v_maxRecDepth_425_);
v_ref_426_ = lean_ctor_get(v_a_418_, 5);
lean_inc(v_ref_426_);
v_currNamespace_427_ = lean_ctor_get(v_a_418_, 6);
lean_inc(v_currNamespace_427_);
v_openDecls_428_ = lean_ctor_get(v_a_418_, 7);
lean_inc(v_openDecls_428_);
v_initHeartbeats_429_ = lean_ctor_get(v_a_418_, 8);
lean_inc(v_initHeartbeats_429_);
v_maxHeartbeats_430_ = lean_ctor_get(v_a_418_, 9);
lean_inc(v_maxHeartbeats_430_);
v_quotContext_431_ = lean_ctor_get(v_a_418_, 10);
lean_inc(v_quotContext_431_);
v_currMacroScope_432_ = lean_ctor_get(v_a_418_, 11);
lean_inc(v_currMacroScope_432_);
v_diag_433_ = lean_ctor_get_uint8(v_a_418_, sizeof(void*)*14);
v_cancelTk_x3f_434_ = lean_ctor_get(v_a_418_, 12);
lean_inc(v_cancelTk_x3f_434_);
v_suppressElabErrors_435_ = lean_ctor_get_uint8(v_a_418_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_436_ = lean_ctor_get(v_a_418_, 13);
lean_inc_ref(v_inheritedTraceOptions_436_);
lean_dec_ref(v_a_418_);
v___x_437_ = lean_nat_dec_eq(v_currRecDepth_424_, v_maxRecDepth_425_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_currRecDepth_424_, v___x_438_);
lean_dec(v_currRecDepth_424_);
v___x_440_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_440_, 0, v_fileName_421_);
lean_ctor_set(v___x_440_, 1, v_fileMap_422_);
lean_ctor_set(v___x_440_, 2, v_options_423_);
lean_ctor_set(v___x_440_, 3, v___x_439_);
lean_ctor_set(v___x_440_, 4, v_maxRecDepth_425_);
lean_ctor_set(v___x_440_, 5, v_ref_426_);
lean_ctor_set(v___x_440_, 6, v_currNamespace_427_);
lean_ctor_set(v___x_440_, 7, v_openDecls_428_);
lean_ctor_set(v___x_440_, 8, v_initHeartbeats_429_);
lean_ctor_set(v___x_440_, 9, v_maxHeartbeats_430_);
lean_ctor_set(v___x_440_, 10, v_quotContext_431_);
lean_ctor_set(v___x_440_, 11, v_currMacroScope_432_);
lean_ctor_set(v___x_440_, 12, v_cancelTk_x3f_434_);
lean_ctor_set(v___x_440_, 13, v_inheritedTraceOptions_436_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*14, v_diag_433_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*14 + 1, v_suppressElabErrors_435_);
lean_inc_ref(v_type_414_);
v___x_441_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_414_, v_useOfNonempty_415_, v_a_416_, v_a_417_, v___x_440_, v_a_419_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref(v___x_441_);
if (lean_obj_tag(v_a_442_) == 1)
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_type_414_);
v_val_443_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_479_ == 0)
{
v___x_445_ = v_a_442_;
v_isShared_446_ = v_isSharedCheck_479_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_a_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_479_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint8_t v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = 1;
v___x_448_ = 1;
v___x_449_ = l_Lean_Meta_mkLetFVars(v_insts_413_, v_val_443_, v___x_447_, v___x_447_, v___x_448_, v_a_416_, v_a_417_, v___x_440_, v_a_419_);
lean_dec_ref(v_insts_413_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = l_Lean_Meta_mkLambdaFVars(v_xs_412_, v_a_450_, v___x_437_, v___x_447_, v___x_437_, v___x_447_, v___x_448_, v_a_416_, v_a_417_, v___x_440_, v_a_419_);
lean_dec_ref(v___x_440_);
lean_dec_ref(v_xs_412_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_a_452_);
v___x_457_ = v___x_445_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_del_object(v___x_445_);
v_a_463_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_451_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_451_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_445_);
lean_dec_ref(v___x_440_);
lean_dec_ref(v_xs_412_);
v_a_471_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_449_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_449_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_a_442_);
v___x_480_ = l_Lean_Meta_whnfCore(v_type_414_, v_a_416_, v_a_417_, v___x_440_, v_a_419_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; uint8_t v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
v___x_482_ = l_Lean_Expr_isForall(v_a_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_481_, v___x_437_, v_a_416_, v_a_417_, v___x_440_, v_a_419_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_494_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_494_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
if (lean_obj_tag(v_a_484_) == 1)
{
lean_object* v_val_488_; 
lean_del_object(v___x_486_);
v_val_488_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_val_488_);
lean_dec_ref(v_a_484_);
v_type_414_ = v_val_488_;
v_a_418_ = v___x_440_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec(v_a_484_);
lean_dec_ref(v___x_440_);
lean_dec_ref(v_insts_413_);
lean_dec_ref(v_xs_412_);
v___x_490_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec_ref(v___x_440_);
lean_dec_ref(v_insts_413_);
lean_dec_ref(v_xs_412_);
return v___x_483_;
}
}
else
{
lean_object* v___x_495_; lean_object* v___f_496_; lean_object* v___x_497_; 
v___x_495_ = lean_box(v_useOfNonempty_415_);
v___f_496_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed), 10, 3);
lean_closure_set(v___f_496_, 0, v_xs_412_);
lean_closure_set(v___f_496_, 1, v_insts_413_);
lean_closure_set(v___f_496_, 2, v___x_495_);
v___x_497_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_a_481_, v___f_496_, v___x_437_, v_a_416_, v_a_417_, v___x_440_, v_a_419_);
lean_dec_ref(v___x_440_);
return v___x_497_;
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v___x_440_);
lean_dec_ref(v_insts_413_);
lean_dec_ref(v_xs_412_);
v_a_498_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_480_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_480_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_440_);
lean_dec_ref(v_type_414_);
lean_dec_ref(v_insts_413_);
lean_dec_ref(v_xs_412_);
return v___x_441_;
}
}
else
{
lean_object* v___x_506_; 
lean_dec_ref(v_inheritedTraceOptions_436_);
lean_dec(v_cancelTk_x3f_434_);
lean_dec(v_currMacroScope_432_);
lean_dec(v_quotContext_431_);
lean_dec(v_maxHeartbeats_430_);
lean_dec(v_initHeartbeats_429_);
lean_dec(v_openDecls_428_);
lean_dec(v_currNamespace_427_);
lean_dec(v_maxRecDepth_425_);
lean_dec(v_currRecDepth_424_);
lean_dec_ref(v_options_423_);
lean_dec_ref(v_fileMap_422_);
lean_dec_ref(v_fileName_421_);
lean_dec_ref(v_type_414_);
lean_dec_ref(v_insts_413_);
lean_dec_ref(v_xs_412_);
v___x_506_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_426_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(lean_object* v_xs_507_, lean_object* v_xs_x27_508_, lean_object* v_insts_509_, lean_object* v_type_x27_510_, uint8_t v_useOfNonempty_511_, lean_object* v_insts_x27_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = l_Array_append___redArg(v_xs_507_, v_xs_x27_508_);
v___x_519_ = l_Array_append___redArg(v_insts_509_, v_insts_x27_512_);
lean_inc_ref(v___y_515_);
v___x_520_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v___x_518_, v___x_519_, v_type_x27_510_, v_useOfNonempty_511_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed(lean_object* v_xs_521_, lean_object* v_xs_x27_522_, lean_object* v_insts_523_, lean_object* v_type_x27_524_, lean_object* v_useOfNonempty_525_, lean_object* v_insts_x27_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v_useOfNonempty_boxed_532_; lean_object* v_res_533_; 
v_useOfNonempty_boxed_532_ = lean_unbox(v_useOfNonempty_525_);
v_res_533_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_521_, v_xs_x27_522_, v_insts_523_, v_type_x27_524_, v_useOfNonempty_boxed_532_, v_insts_x27_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v_insts_x27_526_);
lean_dec_ref(v_xs_x27_522_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(lean_object* v_xs_534_, lean_object* v_insts_535_, uint8_t v_useOfNonempty_536_, lean_object* v_xs_x27_537_, lean_object* v_type_x27_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v___x_544_ = lean_box(v_useOfNonempty_536_);
lean_inc_ref(v_xs_x27_537_);
v___f_545_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_545_, 0, v_xs_534_);
lean_closure_set(v___f_545_, 1, v_xs_x27_537_);
lean_closure_set(v___f_545_, 2, v_insts_535_);
lean_closure_set(v___f_545_, 3, v_type_x27_538_);
lean_closure_set(v___f_545_, 4, v___x_544_);
v___x_546_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_x27_537_, v___f_545_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(lean_object* v_xs_547_, lean_object* v_insts_548_, lean_object* v_type_549_, lean_object* v_useOfNonempty_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
uint8_t v_useOfNonempty_boxed_556_; lean_object* v_res_557_; 
v_useOfNonempty_boxed_556_ = lean_unbox(v_useOfNonempty_550_);
v_res_557_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_547_, v_insts_548_, v_type_549_, v_useOfNonempty_boxed_556_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(lean_object* v_msgData_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v_env_565_; lean_object* v___x_566_; lean_object* v_mctx_567_; lean_object* v_lctx_568_; lean_object* v_options_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_564_ = lean_st_ref_get(v___y_562_);
v_env_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_env_565_);
lean_dec(v___x_564_);
v___x_566_ = lean_st_ref_get(v___y_560_);
v_mctx_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_mctx_567_);
lean_dec(v___x_566_);
v_lctx_568_ = lean_ctor_get(v___y_559_, 2);
v_options_569_ = lean_ctor_get(v___y_561_, 2);
lean_inc_ref(v_options_569_);
lean_inc_ref(v_lctx_568_);
v___x_570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_570_, 0, v_env_565_);
lean_ctor_set(v___x_570_, 1, v_mctx_567_);
lean_ctor_set(v___x_570_, 2, v_lctx_568_);
lean_ctor_set(v___x_570_, 3, v_options_569_);
v___x_571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_msgData_558_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_ref_586_; lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
v_ref_586_ = lean_ctor_get(v___y_583_, 5);
v___x_587_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_inc(v_ref_586_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_ref_586_);
lean_ctor_set(v___x_592_, 1, v_a_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 1);
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg___boxed(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_603_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__0));
v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__2));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4(void){
_start:
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = 0;
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1));
v___x_612_ = l_Lean_MessageData_ofConstName(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__5));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9(void){
_start:
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = 0;
v___x_620_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__8));
v___x_621_ = l_Lean_MessageData_ofConstName(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__10));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__12));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0(lean_object* v_xs_628_, lean_object* v_type_629_, lean_object* v_failedToMessage_630_, lean_object* v_insts_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_637_; lean_object* v___y_639_; lean_object* v___x_679_; 
v___x_637_ = 0;
lean_inc_ref(v___y_634_);
lean_inc_ref(v_type_629_);
lean_inc_ref(v_insts_631_);
lean_inc_ref(v_xs_628_);
v___x_679_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_628_, v_insts_631_, v_type_629_, v___x_637_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
if (lean_obj_tag(v_a_680_) == 0)
{
uint8_t v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v___x_679_);
v___x_681_ = 1;
lean_inc_ref(v___y_634_);
lean_inc_ref(v_type_629_);
lean_inc_ref(v_xs_628_);
v___x_682_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_628_, v_insts_631_, v_type_629_, v___x_681_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
v___y_639_ = v___x_682_;
goto v___jp_638_;
}
else
{
lean_dec_ref(v_a_680_);
lean_dec_ref(v_insts_631_);
v___y_639_ = v___x_679_;
goto v___jp_638_;
}
}
else
{
lean_dec_ref(v_insts_631_);
v___y_639_ = v___x_679_;
goto v___jp_638_;
}
v___jp_638_:
{
if (lean_obj_tag(v___y_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_670_; 
v_a_640_ = lean_ctor_get(v___y_639_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___y_639_);
if (v_isSharedCheck_670_ == 0)
{
v___x_642_ = v___y_639_;
v_isShared_643_ = v_isSharedCheck_670_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___y_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_670_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
if (lean_obj_tag(v_a_640_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_646_; 
lean_dec_ref(v_failedToMessage_630_);
lean_dec_ref(v_type_629_);
lean_dec_ref(v_xs_628_);
v_val_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_val_644_);
lean_dec_ref(v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_val_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
uint8_t v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_642_);
lean_dec(v_a_640_);
v___x_648_ = 1;
v___x_649_ = 1;
v___x_650_ = l_Lean_Meta_mkForallFVars(v_xs_628_, v_type_629_, v___x_637_, v___x_648_, v___x_648_, v___x_649_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec_ref(v_xs_628_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__1, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v_failedToMessage_630_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_indentExpr(v_a_651_);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__3, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__4, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__6, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__9, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__11, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_658_);
v___x_667_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__13, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v___x_668_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_669_;
}
else
{
lean_dec_ref(v_failedToMessage_630_);
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_failedToMessage_630_);
lean_dec_ref(v_type_629_);
lean_dec_ref(v_xs_628_);
v_a_671_ = lean_ctor_get(v___y_639_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___y_639_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___y_639_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___y_639_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___boxed(lean_object* v_xs_683_, lean_object* v_type_684_, lean_object* v_failedToMessage_685_, lean_object* v_insts_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Elab_mkInhabitantFor___lam__0(v_xs_683_, v_type_684_, v_failedToMessage_685_, v_insts_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor(lean_object* v_failedToMessage_693_, lean_object* v_xs_694_, lean_object* v_type_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
lean_inc_ref(v_xs_694_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Elab_mkInhabitantFor___lam__0___boxed), 9, 3);
lean_closure_set(v___f_701_, 0, v_xs_694_);
lean_closure_set(v___f_701_, 1, v_type_695_);
lean_closure_set(v___f_701_, 2, v_failedToMessage_693_);
v___x_702_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_694_, v___f_701_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___boxed(lean_object* v_failedToMessage_703_, lean_object* v_xs_704_, lean_object* v_type_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_mkInhabitantFor(v_failedToMessage_703_, v_xs_704_, v_type_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(lean_object* v_00_u03b1_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___boxed(lean_object* v_00_u03b1_720_, lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(v_00_u03b1_720_, v_msg_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_727_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
}
#ifdef __cplusplus
}
#endif
